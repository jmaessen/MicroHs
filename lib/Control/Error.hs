-- Copyright 2023 Lennart Augustsson
-- See LICENSE file for full license.
module Control.Error(error, errorWithoutStackTrace, undefined, ErrorCall(..)) where
import qualified Prelude()              -- do not import Prelude
import Data.Char_Type
import Data.List_Type
import Control.Exception.Internal
import {-# SOURCE #-} Data.Typeable
import Text.Show

newtype ErrorCall = ErrorCall String
  deriving (Typeable)

instance Show ErrorCall where
  show (ErrorCall s) = ("error: "::String) ++ s

instance Exception ErrorCall

error :: forall a . String -> a
error s = throw (ErrorCall s)

undefined :: forall a . a
undefined = error "undefined"

-- GHC compatibility
errorWithoutStackTrace :: forall a . String -> a
errorWithoutStackTrace = error
