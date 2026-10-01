/****************************************************************************
*
*  This code is Public Domain.
*
*  ========================================================================
*
* Description:  preprocessor
*
****************************************************************************/

#include <ctype.h>
#include <stdarg.h>
#include <stdint.h>

#include "globals.h"
#include "memalloc.h"
#include "parser.h"
#include "condasm.h"
#include "tokenize.h"
#include "equate.h"
#include "macro.h"
#include "input.h"
#include "fastpass.h"
#include "listing.h"
#include "proc.h"
#include "expreval.h"
#include "assume.h"

#define REMOVECOMENT 0

#define MAX_EQUATE_DEPTH 100

extern ret_code (* const directive_tab[])( int, struct asm_tok[] );

#ifdef DEBUG_OUT
int_32 cntppl0;
int_32 cntppl1;
int_32 cntppl2;
#endif

ret_code WriteCodeLabel( char *line, struct asm_tok tokenarray[] )
{
    int oldcnt;
    int oldtoken;
    char oldchar;

    if ( tokenarray[0].token != T_ID ) {
        return( EmitErr( SYNTAX_ERROR_EX, tokenarray[0].string_ptr ) );
    }
    if ( CurrFile[LST] ) LstWrite( LSTTYPE_LABEL, 0, NULL );
    oldcnt = Token_Count;
    oldtoken = tokenarray[2].token;
    oldchar = *tokenarray[2].tokpos;
    Token_Count = 2;
    tokenarray[2].token = T_FINAL;
    *tokenarray[2].tokpos = NULLC;
    ParseLine( tokenarray );
    if ( Options.preprocessor_stdout == TRUE )
        WritePreprocessedLine( line );
    Token_Count = oldcnt;
    tokenarray[2].token = oldtoken;
    *tokenarray[2].tokpos = oldchar;
    return( NOT_ERROR );
}

int VerifyBrackets(struct asm_tok tokenarray[], int openIdx, bool inParam)
{
	int i = openIdx;
	int opCnt = 0;
	if (tokenarray[i].token != T_OP_BRACKET)
	{
		EmitErr(MISSING_LEFT_PARENTHESIS_IN_EXPRESSION);
		return(-1);
	}

	if (!inParam)
	{
		for (i = 0;i < openIdx;i++)
		{
			if (tokenarray[i].token == T_OP_BRACKET || tokenarray[i].token == '(')
				opCnt++;
		}
	}

	if (tokenarray[i + 1].token == T_CL_BRACKET)
		return(i + 1);

	for (i = Token_Count-1;i > openIdx; i--)
	{
		if (tokenarray[i].token == T_CL_BRACKET && opCnt == 0)
			return(i);
		else if (tokenarray[i].token == T_CL_BRACKET)
			opCnt--;
	}

	EmitErr(MISSING_RIGHT_PARENTHESIS_IN_EXPRESSION);
	return(-1);
}

static void VerifyNesting(char *line, bool exprBracket)
{
	int depth = 0;
	int maxdepth = (exprBracket) ? 3 : 2;
	char *p = line;

	if ((Options.output_format == OFORMAT_ELF || Options.output_format == OFORMAT_MAC) && Options.sub_format == SFORMAT_64BIT)
		maxdepth = (exprBracket) ? 2 : 1;

	if (Options.sub_format != SFORMAT_64BIT)
		maxdepth = (exprBracket) ? 2 : 1;

	while (*p)
	{
		if (*p == '(')
			depth++;
		if (*p == ')')
			depth--;
		if (depth > maxdepth)
		{
			EmitErr(MAX_C_NESTING);
			return;
		}
		p++;
	}
}

static void ExpandObjCalls(char *line, struct asm_tok tokenarray[])
{
	int i,j;
	struct dsym *sym;                       /* was correct originally */
	struct dsym *type = NULL;               /* was correct originally */
	struct dsym *tsym;                      /* was correct originally */
	struct dsym *param;                     /* was correct originally */
	bool foundType = FALSE;
	bool foundProc = FALSE;
	int derefCount = 0;
	int opIdx = 0;
	int clIdx = 0;
	int clSqIdx = 0;
	int opSqIdx = 0;
	char newline[MAX_LINE_LEN];
	bool gotOpen = FALSE;
	bool gotClose = FALSE;
	bool gotCloseSqr = FALSE;
	bool gotOpenSqr = FALSE;
	char methodName[MAX_LINE_LEN];
	char indirectAddr[MAX_LINE_LEN];
	char *pMethodStr = methodName;
	char *pStr = newline;
	char *pType = NULL;
	bool inExpr = FALSE;
	bool hasExprBracket = FALSE;
	bool inParam = FALSE;
	bool inProc = FALSE;
	int firstDeRefIdx = 0;
	int paramCount = 0;
	char pcs[16];
	bool didExpand = TRUE;
	char refStr[MAX_LINE_LEN];
	char *pRefStr = refStr;
	struct sfield *field = NULL;

	strcpy(newline, line);

	while (didExpand)
	{
		memset(&indirectAddr, 0, MAX_LINE_LEN);
		memset(&methodName, 0, MAX_LINE_LEN);
		memset(&newline, 0, MAX_LINE_LEN);
		memset(&refStr, 0, MAX_LINE_LEN);
		pStr = newline;
		pRefStr = refStr;
		didExpand = FALSE;
		paramCount = 0;
		inExpr = FALSE;
		inParam = FALSE;
		inProc = FALSE;
		hasExprBracket = FALSE;
		derefCount = 0;
		firstDeRefIdx = 0;
		type = NULL;
		field = NULL;

		for (i = 0; i < Token_Count; i++)
		{
			if (tokenarray[i].token == T_POINTER)
			{
				if (i > 0)
				{
					for (j = i - 1; j >= 0; j--)
					{
						tsym = (struct dsym *)SymCheck(tokenarray[j].string_ptr);
						if (tokenarray[j].token == T_DIRECTIVE && (tokenarray[j].dirtype == DRT_HLLSTART || tokenarray[j].dirtype == DRT_HLLEND))
						{
							inExpr = TRUE;
							if (tokenarray[j + 1].token == T_OP_BRACKET || tokenarray[j + 1].tokval == '(')
								hasExprBracket = TRUE;
							else
								hasExprBracket = FALSE;
							break;
						}
						else if ((tokenarray[j].token == T_DIRECTIVE && tokenarray[j].dirtype == DRT_INVOKE) ||
							strcmp(tokenarray[j].string_ptr, "arginvoke") == 0 ||
							strcmp(tokenarray[j].string_ptr, "_INVOKE") == 0 ||
							strcmp(tokenarray[j].string_ptr, "_I") == 0 ||
							strcmp(tokenarray[j].string_ptr, "_VINVOKE") == 0 ||
							strcmp(tokenarray[j].string_ptr, "_V") == 0 ||
							strcmp(tokenarray[j].string_ptr, "_SINVOKE") == 0 ||
							strcmp(tokenarray[j].string_ptr, "_DEREF") == 0 ||
							strcmp(tokenarray[j].string_ptr, "_DEREFI") == 0 ||
							strcmp(tokenarray[j].string_ptr, "uinvoke") == 0)
						{
							inParam = TRUE;
							break;
						}
						else if (tokenarray[j].token == T_ID && tsym && tsym->sym.isproc)
						{
							inParam = TRUE;
							inProc = TRUE;
							break;
						}
					}
				}

				if(derefCount == 0)
					foundType = FALSE;
				foundProc = FALSE;

				if (i == 0 || (tokenarray[i - 1].token != T_ID &&
				               tokenarray[i - 1].token != T_REG &&
				               tokenarray[i - 1].token != T_CL_SQ_BRACKET))
				{
					EmitError(INVALID_POINTER);
				}
				else if (tokenarray[i - 1].token == T_ID)
				{
					if (derefCount == 0)
					{
						sym = (struct dsym *)SymCheck(tokenarray[i - 1].string_ptr);
						if (sym && sym->sym.target_type && (uintptr_t)sym->sym.target_type > 0x200000 && sym->sym.target_type->isClass)
						{
							foundType = TRUE;
							pType = tokenarray[i - 1].string_ptr;
							type = (struct dsym *)sym->sym.target_type;
							firstDeRefIdx = i - 2;
						}
						else if (sym && sym->sym.type && sym->sym.type->target_type && (uintptr_t)sym->sym.type->target_type > 0x200000 && sym->sym.type->target_type->isClass)
						{
							foundType = TRUE;
							pType = tokenarray[i - 1].string_ptr;
							type = (struct dsym *)sym->sym.type->target_type;
							firstDeRefIdx = i - 2;
						}
						else if (sym && sym->sym.type && sym->sym.type->target_type && (uintptr_t)sym->sym.type->target_type > 0x200000 && sym->sym.type->target_type->isPtrTable)
						{
							foundType = TRUE;
							pType = tokenarray[i - 1].string_ptr;
							type = (struct dsym *)sym->sym.type->target_type;
							firstDeRefIdx = 0;
						}
						else if (sym && (sym->sym.isClass || sym->sym.isPtrTable))
						{
							gotCloseSqr = TRUE;
							gotOpenSqr = FALSE;
							clSqIdx = i - 3;
							for (j = i - 1; j >= 0; j--)
							{
								if (tokenarray[j].token == T_OP_SQ_BRACKET)
								{
									opSqIdx = j;
									gotOpenSqr = TRUE;
									break;
								}
							}
							if (!gotOpenSqr || !gotCloseSqr)
								EmitError(INVALID_POINTER);
							if (sym && (sym->sym.isClass || sym->sym.isPtrTable))
							{
								foundType = TRUE;
								pType = indirectAddr;
								pType = strcpy(pType, "[") + 1;
								for (j = opSqIdx + 1; j < clSqIdx; j++)
								{
									strcpy(pType, tokenarray[j].string_ptr);
									pType += strlen(tokenarray[j].string_ptr);
								}
								pType = strcpy(pType, "]") + 1;
								pType = indirectAddr;
								type = sym;
								firstDeRefIdx = opSqIdx - 1;
							}
							else
								EmitError(INVALID_POINTER);
						}
					}
					else
					{
						bool gotField = FALSE;
						field = type->e.structinfo->head;
						for (; field; field = field->next)
						{
							if (_stricmp(field->sym.name, tokenarray[i - 1].string_ptr) == 0)
							{
								gotField = TRUE;
								break;
							}
						}
						if (gotField)
						{
							type = (struct dsym *)field->sym.target_type;
							if (!type || (uintptr_t)type < 0x10)
								type = (struct dsym *)field->sym.type->target_type;
							if (!type || (uintptr_t)type < 0x10)
								EmitError(INVALID_POINTER);
						}
						else
							EmitError(INVALID_POINTER);

						strcpy(pType + strlen(pType), ".");
						strcpy(pType + strlen(pType), tokenarray[i - 1].string_ptr);
					}
					if (!foundType)
						EmitError(INVALID_POINTER);
				}
				else if (tokenarray[i - 1].token == T_REG)
				{
					sym = (struct dsym *)StdAssumeTable[GetRegNo(tokenarray[i - 1].tokval)].symbol;
					if (sym && sym->sym.target_type)
					{
						foundType = TRUE;
						pType = tokenarray[i - 1].string_ptr;
						type = (struct dsym *)sym->sym.target_type;
						firstDeRefIdx = i - 2;
					}
					else
						EmitError(INVALID_POINTER);
				}
				else if (tokenarray[i - 1].token == T_CL_SQ_BRACKET)
				{
					gotCloseSqr = TRUE;
					gotOpenSqr = FALSE;
					clSqIdx = i - 1;
					for (j = i - 1; j >= 0; j--)
					{
						if (tokenarray[j].token == T_OP_SQ_BRACKET)
						{
							opSqIdx = j;
							gotOpenSqr = TRUE;
							break;
						}
					}
					if (!gotOpenSqr || !gotCloseSqr)
						EmitError(INVALID_POINTER);
					if ((opSqIdx + 1) < Token_Count && tokenarray[opSqIdx + 1].token == T_REG)
					{
						sym = (struct dsym *)StdAssumeTable[GetRegNo(tokenarray[opSqIdx + 1].tokval)].symbol;
						if (sym && sym->sym.target_type)
						{
							foundType = TRUE;
							pType = indirectAddr;
							pType = strcpy(pType, "[") + 1;
							for (j = opSqIdx + 1; j < clSqIdx; j++)
							{
								strcpy(pType, tokenarray[j].string_ptr);
								pType += strlen(tokenarray[j].string_ptr);
							}
							pType = strcpy(pType, "]") + 1;
							pType = indirectAddr;
							type = (struct dsym *)sym->sym.target_type;
							firstDeRefIdx = opSqIdx-1;
						}
						else
							EmitError(INVALID_POINTER);
					}
					else
						EmitError(INVALID_POINTER);
				}

				if (!type || tokenarray[i + 1].token != T_ID)
					EmitError(INVALID_POINTER);
				else
				{
					pMethodStr = methodName;
					pMethodStr = strcpy(pMethodStr, "_") + 1;
					strcpy(pMethodStr, type->sym.name);
					pMethodStr += strlen(type->sym.name);
					pMethodStr = strcpy(pMethodStr, "_") + 1;
					strcpy(pMethodStr, tokenarray[i + 1].string_ptr);
					pMethodStr += strlen(tokenarray[i + 1].string_ptr);
					pMethodStr = methodName;

					sym = (struct dsym *)SymCheck(pMethodStr);
					if (sym && sym->sym.isproc)
					{
						foundProc = TRUE;
						pMethodStr = tokenarray[i + 1].string_ptr;
						for (param = sym->e.procinfo->paralist; param; param = param->nextparam)
						{
							paramCount++;
						}
					}
					else if (type && type->sym.isClass)
					{
						foundProc = FALSE;
						if (derefCount == 0)
						{
							strcpy(pRefStr, pType);
							pRefStr += strlen(pType);
						}
						else
						{
							pRefStr = strcpy(pRefStr, "rcx") + 3;
						}
						pRefStr = strcpy(pRefStr, ",") + 1;
						strcpy(pRefStr, type->sym.name);
						pRefStr += strlen(type->sym.name);
						strcpy(pType, type->sym.name);
					}
					else
						EmitError(INVALID_POINTER);
				}

				if (foundProc)
				{
					int openCount = 1;
					for (j = i; j < Token_Count; j++)
					{
						if (tokenarray[j].token == T_OP_BRACKET || tokenarray[j].tokval == '(')
						{
							opIdx = j;
							gotOpen = TRUE;
							break;
						}
					}

					for (j = opIdx + 1; j < Token_Count; j++)
					{
						if (tokenarray[j].token == T_CL_BRACKET || tokenarray[j].tokval == ')')
							openCount--;

						if (tokenarray[j].token == T_OP_BRACKET || tokenarray[j].tokval == '(')
							openCount++;

						if (openCount == 0)
						{
							clIdx = j;
							gotClose = TRUE;
							break;
						}
					}

					if (!gotOpen)
						EmitError(MISSING_LEFT_PARENTHESIS_IN_EXPRESSION);
					if (!gotClose)
						EmitError(MISSING_RIGHT_PARENTHESIS_IN_EXPRESSION);
				}

				if (foundProc)
				{
					if (!type->sym.isPtrTable)
					{
						for (j = 0; j <= firstDeRefIdx; j++)
						{
							pStr = strcpy(pStr, " ") + 1;
							strcpy(pStr, tokenarray[j].string_ptr);
							pStr += strlen(tokenarray[j].string_ptr);
							pStr = strcpy(pStr, " ") + 1;
						}
					}
					if (inExpr || inParam)
						pStr = strcpy(pStr, "_DEREFI(") + 8;
					else if (!type->sym.isPtrTable)
						pStr = strcpy(pStr, "_DEREF ") + 7;
					else if (type->sym.isPtrTable)
					{
						if (tokenarray[i - 3].token == T_CL_SQ_BRACKET)
						{
							pStr = strcpy(pStr, "_DEREFRR ") + 9;
							strcpy(pStr, pType);
							pStr += strlen(pType);
							pStr = strcpy(pStr, ",") + 1;
						}
						else
						{
							pStr = strcpy(pStr, "_DEREFR ") + 8;
							strcpy(pStr, tokenarray[i - 1].string_ptr);
							pStr += strlen(tokenarray[i - 1].string_ptr);
							pStr = strcpy(pStr, ",") + 1;
						}
					}
					strcpy(pStr, type->sym.name);
					pStr += strlen(type->sym.name);
					pStr = strcpy(pStr, ",") + 1;
					strcpy(pStr, pMethodStr);
					pStr += strlen(pMethodStr);
					pStr = strcpy(pStr, ",") + 1;

					if(type->sym.isPtrTable)
						sprintf(pcs, "%d", paramCount);
					else
						sprintf(pcs, "%d", paramCount - 1);
					strcpy(pStr, pcs);
					pStr += strlen(pcs);

					pStr = strcpy(pStr, ",") + 1;

					if ((paramCount - 1) == 0 && !type->sym.isPtrTable)
					{
						pStr = strcpy(pStr, "0") + 1;
					}
					else if(!type->sym.isPtrTable)
						pStr = strcpy(pStr, "0,") + 2;

					for (j = opIdx + 1; j < clIdx; j++)
					{
						if (*tokenarray[j].string_ptr == '&')
							pStr = strcpy(pStr, " ADDR ") + 6;
						else
						{
							strcpy(pStr, tokenarray[j].string_ptr);
							pStr += strlen(tokenarray[j].string_ptr);
							if (strncmp(tokenarray[j].string_ptr, "ADDR",4) == 0)
								pStr = strcpy(pStr, " ") + 1;
						}
					}

					if(!type->sym.isPtrTable)
						pStr = strcpy(pStr, ",") + 1;

					if (derefCount > 0)
					{
						strcpy(pStr, refStr);
						pStr += strlen(refStr);
						pStr = strcpy(pStr, ",") + 1;
					}
					if (derefCount == 0 && !type->sym.isPtrTable)
					{
						strcpy(pStr, pType);
						pStr += strlen(pType);
						pStr = strcpy(pStr, ",") + 1;
						strcpy(pStr, type->sym.name);
						pStr += strlen(type->sym.name);
					}
					else if(!type->sym.isPtrTable)
					{
						pStr = strcpy(pStr, "rcx,") + 4;
						strcpy(pStr, pType);
						pStr += strlen(pType);
					}

					if (inExpr || inParam)
						pStr = strcpy(pStr, ")") + 1;
					for (j = clIdx + 1; j < Token_Count; j++)
					{
						pStr = strcpy(pStr, " ") + 1;
						strcpy(pStr, tokenarray[j].string_ptr);
						pStr += strlen(tokenarray[j].string_ptr);
						pStr = strcpy(pStr, " ") + 1;
					}

					didExpand = TRUE;
					break;
				}

				derefCount++;
			}
		}

		if (didExpand)
		{
			strcpy(line, newline);
			Token_Count = Tokenize(line, 0, tokenarray, TOK_RESCAN);
		}
	}
}

static void ExpandStaticObjCalls(char *line, struct asm_tok tokenarray[])
{
	int i, j;
	struct asym *sym = NULL;              /* SymSearch returns struct asym* */
	int opIdx, clIdx;
	int method;
	int type;
	char newline[MAX_LINE_LEN];
	char *pStr;
	int opCount = 0;
	bool hasParams = FALSE;
	bool inParam = FALSE;
	bool inExpr = FALSE;
	bool inProc = FALSE;
	bool hasExprBracket = FALSE;
	struct dsym *tsym = NULL;

	memset(&newline, 0, MAX_LINE_LEN);
	pStr = newline;

	inParam = FALSE;
	inExpr = FALSE;
	inProc = FALSE;
	hasExprBracket = FALSE;

	for (i = 0; i < Token_Count; i++)
	{
		if (tokenarray[i].token == T_ID)
		{
			sym = SymSearch(tokenarray[i].string_ptr);
			if (sym && sym->isClass)
			{
				if (tokenarray[i + 1].token == T_DOT && tokenarray[i + 2].token == T_ID && tokenarray[i + 3].token == T_OP_BRACKET)
				{
					if (i > 0)
					{
						for (j = i - 1; j >= 0; j--)
						{
							tsym = (struct dsym *)SymCheck(tokenarray[j].string_ptr);
							if (tokenarray[j].token == T_DIRECTIVE && (tokenarray[j].dirtype == DRT_HLLSTART || tokenarray[j].dirtype == DRT_HLLEND))
							{
								inExpr = TRUE;
								if (tokenarray[j + 1].token == T_OP_BRACKET || tokenarray[j + 1].tokval == '(')
									hasExprBracket = TRUE;
								else
									hasExprBracket = FALSE;
								break;
							}
							else if ((tokenarray[j].token == T_DIRECTIVE && tokenarray[j].dirtype == DRT_INVOKE) ||
								strcmp(tokenarray[j].string_ptr, "arginvoke") == 0 ||
								strcmp(tokenarray[j].string_ptr, "_INVOKE") == 0 ||
								strcmp(tokenarray[j].string_ptr, "_I") == 0 ||
								strcmp(tokenarray[j].string_ptr, "_VINVOKE") == 0 ||
								strcmp(tokenarray[j].string_ptr, "_V") == 0 ||
								strcmp(tokenarray[j].string_ptr, "_SINVOKE") == 0 ||
								strcmp(tokenarray[j].string_ptr, "_DEREF") == 0 ||
								strcmp(tokenarray[j].string_ptr, "_DEREFI") == 0 ||
								strcmp(tokenarray[j].string_ptr, "uinvoke") == 0)
							{
								inParam = TRUE;
								break;
							}
							else if (tokenarray[j].token == T_ID && tsym && tsym->sym.isproc)
							{
								inParam = TRUE;
								inProc = TRUE;
								break;
							}
						}
					}

					if (tokenarray[i - 1].token == T_COMMA)
						inExpr = TRUE;

					if (i > 0)
					{
						for (j = i - 1; j >= 0; j--)
						{
							if (tokenarray[j].token == T_OP_SQ_BRACKET)
							{
								inExpr = TRUE;
								break;
							}
						}
					}

					opIdx = i + 3;
					method = i + 2;
					type = i;

					opCount = 1;
					clIdx = -1;
					for (j = opIdx + 1; j < Token_Count; j++)
					{
						if (tokenarray[j].token == T_OP_BRACKET)
							opCount++;
						else if (tokenarray[j].token == T_CL_BRACKET)
							opCount--;
						if (opCount == 0)
						{
							clIdx = j;
							break;
						}
					}
					if (clIdx < 0)
						continue;

					if (clIdx > opIdx + 1)
						hasParams = TRUE;

					for (j = 0; j < i; j++)
					{
						pStr = strcpy(pStr, tokenarray[j].string_ptr);
						pStr += strlen(tokenarray[j].string_ptr);
						pStr = strcpy(pStr, " ") + 1;
					}

					if(inProc || inParam || inExpr)
						pStr = strcpy(pStr, "_STATIC(") + 8;
					else
						pStr = strcpy(pStr, "_SINVOKE ") + 9;
					strcpy(pStr, tokenarray[type].string_ptr);
					pStr += strlen(tokenarray[type].string_ptr);
					pStr = strcpy(pStr, ",") + 1;
					strcpy(pStr, tokenarray[method].string_ptr);
					pStr += strlen(tokenarray[method].string_ptr);
					if (hasParams)
					{
						pStr = strcpy(pStr, ",") + 1;

						for (j = opIdx + 1; j < clIdx; j++)
						{
							if (*tokenarray[j].string_ptr == '&')
								pStr = strcpy(pStr, " ADDR ") + 6;
							else
							{
								pStr = strcpy(pStr, tokenarray[j].string_ptr);
								pStr += strlen(tokenarray[j].string_ptr);
							}
						}
					}
					if (inProc || inParam || inExpr)
						pStr = strcpy(pStr, ")") + 1;

					if (clIdx < Token_Count-1)
					{
						for (i = clIdx+1; i < Token_Count; i++)
						{
							pStr = strcpy(pStr, tokenarray[i].string_ptr);
							pStr += strlen(tokenarray[i].string_ptr);
							pStr = strcpy(pStr, " ") + 1;
						}
					}

					strcpy(line, newline);
					Token_Count = Tokenize(line, 0, tokenarray, TOK_RESCAN);
				}
			}
		}
	}
}

static struct asym * TraverseEquate(struct asym *sym)
{
	struct asym *resultSym = sym;
	int depth = 0;
	if (sym)
	{
		while (resultSym->state == SYM_TMACRO && resultSym->string_ptr != NULL)
		{
			if (++depth > MAX_EQUATE_DEPTH)
				break;
			resultSym = SymLookup(resultSym->string_ptr);
			if (resultSym == NULL)
				break;
		}
	}
	return(resultSym);
}

static void ExpandHllCalls(char *line, struct asm_tok tokenarray[], bool inParam, int argIdx, bool inExpr)
{
	int i, j;
	struct dsym *sym;                     /* was struct dsym originally */
	char newline[MAX_LINE_LEN];
	int clIdx, opIdx;
	char *p = newline;
	char idxStack[] = { 0, 0, 0, 0 };
	int stackPt = -1;
	char idxline[MAX_LINE_LEN];
	char invCnt = 1;
	bool hasExprBracket = FALSE;
	bool expandedCall = FALSE;
	char uCnt = 0;
	char arginvoke_buf[] = "arginvoke(  ,  ,";

	strcpy(newline, line);
	memset(&idxline, 0, MAX_LINE_LEN);

	for (i = 0;i < Token_Count;i++)
	{
		if (tokenarray[i].token == T_ID)
		{
			sym = (struct dsym *)SymCheck(tokenarray[i].string_ptr);

			sym = (struct dsym *)TraverseEquate((struct asym *)sym);

			if(sym && (sym->sym.isproc || (sym->sym.isfunc && sym->sym.state == SYM_EXTERNAL)) && tokenarray[i+1].tokval != T_PROC && tokenarray[i+1].tokval != T_PROTO &&
				tokenarray[i+1].tokval != T_ENDP && tokenarray[i+1].tokval != T_EQU && tokenarray[i+1].token == T_OP_BRACKET)
			{
				if (i > 0)
				{
					for (j = i - 1;j >= 0;j--)
					{
						if (tokenarray[j].token == T_DIRECTIVE && (tokenarray[j].dirtype == DRT_HLLSTART || tokenarray[j].dirtype == DRT_HLLEND))
						{
							inExpr = TRUE;
							if (tokenarray[j + 1].token == T_OP_BRACKET || tokenarray[j + 1].tokval == '(')
								hasExprBracket = TRUE;
							else
								hasExprBracket = FALSE;
							break;
						}
						else if ((tokenarray[j].token == T_DIRECTIVE && tokenarray[j].dirtype == DRT_INVOKE) ||
							strcmp(tokenarray[j].string_ptr, "arginvoke") == 0 ||
							strcmp(tokenarray[j].string_ptr, "_INVOKE") == 0 ||
							strcmp(tokenarray[j].string_ptr, "_I") == 0 ||
							strcmp(tokenarray[j].string_ptr, "_VINVOKE") == 0 ||
							strcmp(tokenarray[j].string_ptr, "_SINVOKE") == 0 ||
							strcmp(tokenarray[j].string_ptr, "_V") == 0 ||
							strcmp(tokenarray[j].string_ptr, "_DEREF") == 0 ||
							strcmp(tokenarray[j].string_ptr, "_DEREFI") == 0 ||
							strcmp(tokenarray[j].string_ptr, "uinvoke") == 0)
						{
							inParam = TRUE;
							break;
						}
					}
				}

				if (i > 0 && (tokenarray[i - 1].token == T_COLON || tokenarray[i - 1].tokval == T_EQU ||
					tokenarray[i - 1].tokval == T_INVOKE || tokenarray[i - 1].token == T_INSTRUCTION || tokenarray[i - 1].tokval == T_ADDR ||
					tokenarray[i - 1].tokval == T_OFFSET || tokenarray[i - 1].tokval == T_PTR || tokenarray[i - 1].tokval == T_END ||
					(tokenarray[i - 1].token == T_DIRECTIVE && tokenarray[i - 1].dirtype == DRT_DATADIR) || tokenarray[i - 1].token == T_UNARY_OPERATOR ||  tokenarray[i - 1].tokval == T_PROC ||
					strcmp(tokenarray[i - 1].string_ptr,"arginvoke") == 0 || strcmp(tokenarray[i - 1].string_ptr, "@what") == 0)) continue;

				if (tokenarray[i - 1].token == T_COMMA)
					inExpr = TRUE;

				if (i > 0)
				{
					for (j = i - 1;j >= 0;j--)
					{
						if (tokenarray[j].token == T_OP_SQ_BRACKET)
						{
							inExpr = TRUE;
							break;
						}
					}
				}

				opIdx = i + 1;
				clIdx = VerifyBrackets(tokenarray, opIdx, inParam);
				if (clIdx == -1)
					return;

				expandedCall = TRUE;

				for (j = opIdx; j < clIdx; j++)
				{
					if (*(tokenarray[j].string_ptr) == '&')
					{
						tokenarray[j].string_ptr = (char *)"ADDR ";
					}
				}

				if (!inParam && !inExpr)
				{
					for (j = clIdx; j > i; j--)
						tokenarray[j] = tokenarray[j - 1];

					if (clIdx > opIdx + 1)
					{
						tokenarray[clIdx + 1].token = T_FINAL;
						tokenarray[opIdx + 1].string_ptr = (char *)",";
						tokenarray[opIdx + 1].token = T_COMMA;
					}
					else
					{
						tokenarray[opIdx + 1].string_ptr = (char *)"";
						tokenarray[opIdx + 1].token = T_FINAL;
					}
					tokenarray[i].token = T_DIRECTIVE;
					tokenarray[i].tokval = T_INVOKE;
					tokenarray[i].dirtype = DRT_INVOKE;
					tokenarray[i].string_ptr = (char *)"invoke";
				}
				else
				{
					for (j = Token_Count; j > i; j--)
						tokenarray[j] = tokenarray[j - 1];

					for (j = Token_Count+1; j > i; j--)
						tokenarray[j] = tokenarray[j - 1];

					Token_Count+=2;
					tokenarray[Token_Count].string_ptr = (char *)"";
					tokenarray[Token_Count].token = T_FINAL;
					if (clIdx > opIdx + 1)
					{
						tokenarray[opIdx + 2].string_ptr = (char *)",";
						tokenarray[opIdx + 2].token = T_COMMA;
					}
					else
					{
						tokenarray[opIdx + 2].string_ptr = (char *)" ";
					}
					tokenarray[i].token = T_ID;
					tokenarray[i].tokval = 0;
					tokenarray[i].dirtype = 0;
					if (inExpr && !inParam)
					{
						tokenarray[i].string_ptr = (char *)"uinvoke";
						tokenarray[i + 1].string_ptr = (char *)"(";
						tokenarray[i + 1].token = '(';
						uCnt++;
						if (uCnt > 1)
						{
							EmitErr(MAX_C_CALLS);
						}
					}
					else if (inParam)
					{
						tokenarray[i].string_ptr = arginvoke_buf;
						tokenarray[i + 1].string_ptr = (char *)"";
						tokenarray[i + 1].token = 0;
					}
				}

				i += 2;

				for (j = 0;j < Token_Count; j++)
				{
					if (tokenarray[j].tokval == T_PTR)
					{
						strcpy(p, " ");
						p++;
					}
					strcpy(p, tokenarray[j].string_ptr);
					tokenarray[j].tokpos = p;
					p += strlen(tokenarray[j].string_ptr);
					if (j == 0 || tokenarray[j].tokval == T_ADDR || tokenarray[j].tokval == T_OFFSET)
					{
						strcpy(p, " ");
						p++;
					}
				}

				p = newline;
			}
		}
	}

	if (expandedCall)
	{
		p = newline;
		p = strstr(p, "invoke");
		if (p != NULL)
		{
			bool inBrackets = FALSE;
			j = (int)(p - newline);
			if (j >= 0 && j < MAX_LINE_LEN)
			{
				stackPt++;
				idxStack[stackPt] = 0;
				while (*p && j < MAX_LINE_LEN - 1)
				{
					idxline[j++] = idxStack[stackPt];
					if (*p == '(')
						inBrackets = TRUE;
					if (*p == ')')
						inBrackets = FALSE;
					if (!inBrackets && *p == ',')
						idxStack[stackPt]++;
					p++;
				}
			}
		}
		p = newline;
		p = strstr(p, "arginvoke(");
		j = (int)(p - newline);
		while (p)
		{
			if (idxline[j] == 0) idxline[j] = 1;
			*(p + 10) = (char)(((idxline[j] & 0xf0) >> 4) + 48);
			*(p + 11) = (char)(((idxline[j] & 0x0f)) + 48);
			*(p + 13) = (char)(((invCnt & 0xf0) >> 4) + 48);
			*(p + 14) = (char)(((invCnt & 0x0f)) + 48);
			p = strstr(p + 1, "arginvoke(");
			invCnt++;
			j = (int)(p - newline);
		}

		VerifyNesting(newline, hasExprBracket);
	}

	strcpy(line, newline);
}

static bool PossibleCallExpansion(struct asm_tok tokenarray[])
{
	bool result = FALSE;
	bool gotOp = FALSE;
	bool gotCl = FALSE;
	int i = 0;
	for (i = 0;i < Token_Count;i++)
	{
		if (tokenarray[i].token == T_POINTER)
		{
			result = TRUE;
			break;
		}
		if (tokenarray[i].token == T_OP_BRACKET && i > 0)
		{
			if (tokenarray[i - 1].token == T_ID)
			{
				gotOp = TRUE;
			}
		}
		if (tokenarray[i].token == T_CL_BRACKET)
			gotCl = TRUE;
	}

	if (gotOp && gotCl)
		result = TRUE;

	return(result);
}

void EvaluatePreprocessItems(char *line, struct asm_tok tokenarray[])
{
	int i;
	struct dsym *recsym;                  /* was struct dsym originally */
	struct expr opndx[1];

	memset(&opndx, 0, sizeof(opndx));

	for (i = 0;i < Token_Count; i++)
	{
		if (tokenarray[i].token == T_ID)
		{
			recsym = (struct dsym *)SymCheck(tokenarray[i].string_ptr);
			if (recsym && recsym->sym.typekind == TYPE_RECORD && CurrProc)
			{
				if (CurrSeg && (strcmp(CurrSeg->sym.name, "_TEXT") == 0 || strcmp(CurrSeg->sym.name, "_flat") == 0))
				{
					if (EvalOperand(&i, tokenarray, Token_Count, &opndx[0], 0) == ERROR)
						EmitErr(INVALID_INSTRUCTION_OPERANDS);
					recsym->sym.used = FALSE;
				}
			}
		}
	}
}

int PreprocessLine( char *line, struct asm_tok tokenarray[] )
{
    int i;
	char cline[MAX_LINE_LEN];

	ModuleInfo.CurrComment = NULL;
    ModuleInfo.line_flags = 0;

    Token_Count = Tokenize( line, 0, tokenarray, TOK_DEFAULT );

#ifdef DEBUG_OUT
    cntppl0++;
    if ( ModuleInfo.GeneratedCode )
        DebugMsg1(("PreprocessLine: >%s<\n", line ));
    else
        DebugMsg1(("PreprocessLine(%s): >%s< cmt=%s\n", GetTopSrcName(), line, ModuleInfo.CurrComment ? ModuleInfo.CurrComment : "" ));
#endif

#if REMOVECOMENT == 0
    if ( Token_Count == 0 && ( CurrIfState == BLOCK_ACTIVE || ModuleInfo.listif ) )
        LstWriteSrcLine();
#endif

    if ( Token_Count == 0 )
        return( 0 );

#ifdef DEBUG_OUT
    if ( Options.skip_preprocessor )
        return( Token_Count );
#endif

	if (!Options.nomlib && Options.hlcall)
	{
		if (CurrSeg && (strcmp(CurrSeg->sym.name, "_TEXT") == 0 || strcmp(CurrSeg->sym.name, "_flat") == 0) && PossibleCallExpansion( tokenarray ))
		{
			strcpy(cline, line);
			ExpandStaticObjCalls(cline, tokenarray);
			if (strcmp(cline, line) != 0)
			{
				strcpy(line, cline);
				Token_Count = Tokenize(line, 0, tokenarray, TOK_RESCAN);
			}
			ExpandObjCalls(cline, tokenarray);
			if (strcmp(cline, line) != 0)
			{
				strcpy(line, cline);
				Token_Count = Tokenize(line, 0, tokenarray, TOK_RESCAN);
			}
			ExpandHllCalls(cline, tokenarray, FALSE, 0, FALSE);
			if (strcmp(cline, line) != 0)
			{
				strcpy(line, cline);
				Token_Count = Tokenize(line, 0, tokenarray, TOK_RESCAN);
			}
		}
	}

	EvaluatePreprocessItems( line, tokenarray );

    if ( CurrIfState == BLOCK_ACTIVE )
	{
        if ( ( tokenarray[Token_Count].bytval & TF3_EXPANSION ? ExpandText( line, tokenarray, TRUE ) : ExpandLine( line, tokenarray ) ) < NOT_ERROR )
            return( 0 );
    }

    DebugCmd( cntppl1++ );

    i = 0;
    if ( Token_Count > 2 && ( tokenarray[1].token == T_COLON || tokenarray[1].token == T_DBL_COLON ) )
        i = 2;

    if ( tokenarray[i].token == T_DIRECTIVE && tokenarray[i].dirtype <= DRT_INCLUDE )
	{
        if ( i > 1 )
		{
            if ( ERROR == WriteCodeLabel( line, tokenarray ) )
                return( 0 );
        }
        directive_tab[tokenarray[i].dirtype]( i, tokenarray );
        return( 0 );
    }

    if ( tokenarray[0].token == T_ID && tokenarray[1].token == T_DIRECTIVE )
	{
        struct asym *sym;
        switch ( tokenarray[1].dirtype ) {
        case DRT_EQU:
            if ( sym = CreateConstant( tokenarray ) ) {
                if ( sym->state != SYM_TMACRO ) {
#if FASTPASS
                    if ( StoreState ) FStoreLine( 0 );
#endif
                    if ( Options.preprocessor_stdout == TRUE )
                        WritePreprocessedLine( line );
                }
                if ( ModuleInfo.list == TRUE ) {
                    LstWrite( sym->state == SYM_INTERNAL ? LSTTYPE_EQUATE : LSTTYPE_TMACRO, 0, sym );
                }
            }
            return( 0 );
        case DRT_MACRO:
        case DRT_CATSTR:
        case DRT_SUBSTR:
            directive_tab[tokenarray[1].dirtype]( 1, tokenarray );
            return( 0 );
        }
    }

    DebugCmd( cntppl2++ );
    return( Token_Count );
}