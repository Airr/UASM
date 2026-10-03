/****************************************************************************
*
*                            Open Watcom Project
*
*    Portions Copyright (c) 1983-2002 Sybase, Inc. All Rights Reserved.
*
*  ========================================================================
*
*    This file contains Original Code and/or Modifications of Original
*    Code as defined in and that are subject to the Sybase Open Watcom
*    Public License version 1.0 (the 'License'). You may not use this file
*    except in compliance with the License. BY USING THIS FILE YOU AGREE TO
*    ALL TERMS AND CONDITIONS OF THE LICENSE. A copy of the License is
*    provided with the Original Code and Modifications, and is also
*    available at www.sybase.com/developer/opensource.
*
*    The Original Code and all software distributed under the License are
*    distributed on an 'AS IS' basis, WITHOUT WARRANTY OF ANY KIND, EITHER
*    EXPRESS OR IMPLIED, AND SYBASE AND ALL CONTRIBUTORS HEREBY DISCLAIM
*    ALL SUCH WARRANTIES, INCLUDING WITHOUT LIMITATION, ANY WARRANTIES OF
*    MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, QUIET ENJOYMENT OR
*    NON-INFRINGEMENT. Please see the License for the specific language
*    governing rights and limitations under the License.
*
*  ========================================================================
*
* Description:  defines bool, TRUE and FALSE
*               This file is included by globals.h
*
****************************************************************************/


// 1. Handle the 'bool' type safely across modern and legacy compilers
#if defined(__cplusplus) || (defined(__STDC_VERSION__) && __STDC_VERSION__ >= 202000L) || (defined(__GNUC__) && __GNUC__ >= 14)
    // 'bool' is already a built-in native keyword. Do not typedef it.
#else
    // Legacy fallback for older C standards (C99, C11, Watcom, etc.)
    #if !defined( BOOL_DEFINED ) && !defined( bool ) && !(__WATCOMC__ >= 1070 && defined(__cplusplus))
        #define BOOL_DEFINED
        typedef unsigned char bool;
    #endif
#endif

// 2. Ensure TRUE and FALSE are always defined, adapting to whatever environment we are in
#ifndef TRUE
    #if defined(__cplusplus) || (defined(__STDC_VERSION__) && __STDC_VERSION__ >= 202311L) || (defined(__GNUC__) && __GNUC__ >= 14)
        #define TRUE  true  // Map to native true keyword in modern environments
    #else
        #define TRUE  1     // Fallback for legacy environments
    #endif
#endif

#ifndef FALSE
    #if defined(__cplusplus) || (defined(__STDC_VERSION__) && __STDC_VERSION__ >= 202311L) || (defined(__GNUC__) && __GNUC__ >= 14)
        #define FALSE false // Map to native false keyword in modern environments
    #else
        #define FALSE 0     // Fallback for legacy environments
    #endif
#endif
