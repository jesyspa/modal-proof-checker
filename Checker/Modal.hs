module Checker.Modal where

import Checker.Formula
import Control.Monad.Free

data ModalF f = BoxF f
              | DiamondF f
              deriving (Eq, Functor, Foldable, Traversable)

type ModalFormula = Formula ModalF

fbox, fdiamond :: ModalFormula a -> ModalFormula a
fbox x = Free $ ModalityF (BoxF x)
fdiamond x = Free $ ModalityF (DiamondF x)

