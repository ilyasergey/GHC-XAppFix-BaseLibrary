{-# OPTIONS -fno-implicit-prelude #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  GHC.Unicde
-- Copyright   :  (c) The University of Glasgow, 2003
-- License     :  see libraries/base/LICENSE
-- 
-- Maintainer  :  cvs-ghc@haskell.org
-- Stability   :  internal
-- Portability :  non-portable (GHC extensions)
--
-- Implementations for the character predicates (isLower, isUpper, etc.)
-- and the conversions (toUpper, toLower).  The implementation uses
-- libunicode on Unix systems if that is available.
--
-----------------------------------------------------------------------------

module GHC.Unicode (
    isAscii, isLatin1, isControl,
    isAsciiUpper, isAsciiLower,
    isPrint, isSpace,  isUpper,
    isLower, isAlpha,  isDigit,
    isOctDigit, isHexDigit, isAlphaNum,
    toUpper, toLower,
  ) where

import GHC.Base
import GHC.Real  (fromIntegral)
import GHC.Int
import GHC.Word
import GHC.Num	 (fromInteger)

#include "config.h"

isAscii, isLatin1, isAsciiUpper, isAsciiLower :: Char -> Bool
isAscii c	 	=  c <  '\x80'
isLatin1 c              =  c <= '\xff'
isAsciiLower c          =  c >= 'a' && c <= 'z'
isAsciiUpper c          =  c >= 'A' && c <= 'Z'

isControl, isPrint, isSpace, isUpper,
 isLower, isAlpha, isDigit, isOctDigit, isHexDigit, isAlphaNum
 :: Char -> Bool

isOctDigit c		=  c >= '0' && c <= '7'
isHexDigit c		=  isDigit c || c >= 'A' && c <= 'F' ||
                                        c >= 'a' && c <= 'f'

-- -----------------------------------------------------------------------------
-- Win32 implementation

#if defined(HAVE_WCTYPE_H) || mingw32_TARGET_OS

-- Use the wide-char classification functions if available.  Glibc
-- seems to implement these properly, even for chars > 0xffff, as long
-- as you call setlocale() to set the locale to something other than
-- "C".  Therefore, we call setlocale() in hs_init().

-- Win32 uses UTF-16, so presumably the system-supplied iswlower() and
-- friends won't work properly with characters > 0xffff.  These
-- characters are represented as surrogate pairs in UTF-16.

type WInt = (#type wint_t)
type CInt = (#type int)

isDigit    c = iswdigit (fromIntegral (ord c)) /= 0
isAlpha    c = iswalpha (fromIntegral (ord c)) /= 0
isAlphaNum c = iswalnum (fromIntegral (ord c)) /= 0
isSpace    c = iswspace (fromIntegral (ord c)) /= 0
isControl  c = iswcntrl (fromIntegral (ord c)) /= 0
isPrint    c = iswprint (fromIntegral (ord c)) /= 0
isUpper    c = iswupper (fromIntegral (ord c)) /= 0
isLower    c = iswlower (fromIntegral (ord c)) /= 0

toLower c = chr (fromIntegral (towlower (fromIntegral (ord c))))
toUpper c = chr (fromIntegral (towupper (fromIntegral (ord c))))

foreign import ccall unsafe "iswdigit"
  iswdigit :: WInt -> CInt

foreign import ccall unsafe "iswalpha"
  iswalpha :: WInt -> CInt

foreign import ccall unsafe "iswalnum"
  iswalnum :: WInt -> CInt

foreign import ccall unsafe "iswcntrl"
  iswcntrl :: WInt -> CInt

foreign import ccall unsafe "iswspace"
  iswspace :: WInt -> CInt

foreign import ccall unsafe "iswprint"
  iswprint :: WInt -> CInt

foreign import ccall unsafe "iswlower"
  iswlower :: WInt -> CInt

foreign import ccall unsafe "iswupper"
  iswupper :: WInt -> CInt

foreign import ccall unsafe "towlower"
  towlower :: WInt -> WInt

foreign import ccall unsafe "towupper"
  towupper :: WInt -> WInt

-- -----------------------------------------------------------------------------
-- No libunicode, so fall back to the ASCII-only implementation

#else

isControl c		=  c < ' ' || c >= '\DEL' && c <= '\x9f'
isPrint c		=  not (isControl c)

-- isSpace includes non-breaking space
-- Done with explicit equalities both for efficiency, and to avoid a tiresome
-- recursion with GHC.List elem
isSpace c		=  c == ' '	||
			   c == '\t'	||
			   c == '\n'	||
			   c == '\r'	||
			   c == '\f'	||
			   c == '\v'	||
			   c == '\xa0'

-- The upper case ISO characters have the multiplication sign dumped
-- randomly in the middle of the range.  Go figure.
isUpper c		=  c >= 'A' && c <= 'Z' || 
                           c >= '\xC0' && c <= '\xD6' ||
                           c >= '\xD8' && c <= '\xDE'
-- The lower case ISO characters have the division sign dumped
-- randomly in the middle of the range.  Go figure.
isLower c		=  c >= 'a' && c <= 'z' ||
                           c >= '\xDF' && c <= '\xF6' ||
                           c >= '\xF8' && c <= '\xFF'

isAlpha c		=  isLower c || isUpper c
isDigit c		=  c >= '0' && c <= '9'
isAlphaNum c		=  isAlpha c || isDigit c

-- Case-changing operations

toUpper, toLower	:: Char -> Char
toUpper c@(C## c##)
  | isAsciiLower c    = C## (chr## (ord## c## -## 32##))
  | isAscii c         = c
    -- fall-through to the slower stuff.
  | isLower c	&& c /= '\xDF' && c /= '\xFF'
  = unsafeChr (ord c `minusInt` ord 'a' `plusInt` ord 'A')
  | otherwise
  = c


toLower c@(C## c##)
  | isAsciiUpper c = C## (chr## (ord## c## +## 32##))
  | isAscii c      = c
  | isUpper c	   = unsafeChr (ord c `minusInt` ord 'A' `plusInt` ord 'a')
  | otherwise	   =  c

#endif
