-- Copyright 2024 Lennart Augustsson
-- See LICENSE file for full license.
module Control.Exception.Internal(
  throw, catch,
  Exception(..),
  SomeException(..),
  PatternMatchFail, NoMethodError, RecSelError, RecConError(..),
  patternMatchFail, noMethodError, recSelError, recConError,
  ) where
import Prelude()
import Primitives(IO)
import Data.Char_Type
import Data.List_Type
import Data.Maybe_Type
import {-# SOURCE #-} Data.Typeable
import Text.Show

primRaise :: forall a . SomeException -> a
primRaise = primitive "raise"

primCatch :: forall a . IO a -> (SomeException -> IO a) -> IO a
primCatch = primitive "catch"

throw :: forall e a. Exception e => e -> a
throw e = primRaise (toException e)

catch   :: forall e a .
           Exception e
        => IO a
        -> (e -> IO a)
        -> IO a
catch io handler = primCatch io handler'
    where handler' e = case fromException e of
                       Just e' -> handler e'
                       Nothing -> primRaise e

------------------

data SomeException = forall e . Exception e => SomeException e
  deriving (Typeable)

-- NOTE: The runtime system knows about this class.
-- It uses displayException to show an uncaught exception.
-- Any changes here must be reflected in eval.c
class (Typeable e, Show e) => Exception e where
    toException      :: e -> SomeException
    fromException    :: SomeException -> Maybe e
    displayException :: e -> String

    toException = SomeException
    fromException (SomeException e) = cast e
    displayException = show

------------------

-- Errors generated by the compiler
-- NOTE: Do not change the names or locations of these definitions.
-- The compiler knows about them.

newtype PatternMatchFail = PatternMatchFail String deriving (Typeable)
newtype NoMethodError    = NoMethodError    String deriving (Typeable)
newtype RecSelError      = RecSelError      String deriving (Typeable)
newtype RecConError      = RecConError      String deriving (Typeable)

instance Show PatternMatchFail where showsPrec _ (PatternMatchFail s) r = showString "no match at "     (showString s r)
instance Show NoMethodError    where showsPrec _ (NoMethodError    s) r = showString "no default for "  (showString s r)
instance Show RecSelError      where showsPrec _ (RecSelError      s) r = showString "no field "        (showString s r)
instance Show RecConError      where showsPrec _ (RecConError      s) r = showString "uninit field "    (showString s r)

instance Exception PatternMatchFail
instance Exception NoMethodError
instance Exception RecSelError
instance Exception RecConError

patternMatchFail :: forall a . String -> a
noMethodError    :: forall a . String -> a
recSelError      :: forall a . String -> a
recConError      :: forall a . String -> a

noMethodError    s = throw (NoMethodError    s)
patternMatchFail s = throw (PatternMatchFail s)
recSelError      s = throw (RecSelError      s)
recConError      s = throw (RecConError      s)
