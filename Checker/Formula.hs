module Checker.Formula where

import Control.Monad.Free
import Control.Applicative
import Data.Void
import Data.List (nub, sort)
import Data.Foldable

data FormulaF m r = AndF r r
                  | OrF r r
                  | ImpliesF r r
                  | NotF r
                  | Truth
                  | Falsehood
                  | ModalityF (m r)
                  deriving (Eq, Functor, Foldable, Traversable)



type Formula m = Free (FormulaF m)

type PropF = Const Void
type PropFormula = Formula PropF

evaluateF :: FormulaF PropF Bool -> Bool
evaluateF (AndF x y) = x && y
evaluateF (OrF x y) = x || y
evaluateF (ImpliesF x y) = not x || y
evaluateF (NotF x) = not x
evaluateF Truth = True
evaluateF Falsehood = False
evaluateF (ModalityF m) = absurd (getConst m)

evaluate :: PropFormula Bool -> Bool
evaluate = iter evaluateF

toFun :: Eq a => [(a, b)] -> (a -> b) -> a -> b
toFun s f a = case lookup a s of
                    Just b' -> b'
                    Nothing -> f a

isTautology :: Ord a => PropFormula a -> Bool
isTautology m = all evaluate $ map (\s -> toFun s (error "logic error") <$> m) substs
    where as = nub . sort . toList $ m
          substs = mapM (\(x, xs) -> (x,) <$> xs) . map (\x -> (x, [False, True])) $ as


fand, for, fimplies :: Formula m a -> Formula m a -> Formula m a
fand x y     = Free $ AndF x y
for x y      = Free $ OrF x y
fimplies x y = Free $ ImpliesF x y
fnot :: Formula m a -> Formula m a
fnot x = Free $ NotF x
fmodal :: m (Formula m a) -> Formula m a
fmodal x = Free $ ModalityF x
fvar :: a -> Formula m a
fvar = Pure
ftruth, ffalsehood :: Formula m a
ftruth = Free Truth
ffalsehood = Free Falsehood

(.&.), (.|.), (.->.) :: Formula m a -> Formula m a -> Formula m a
infixl 5 .&.
(.&.) = fand
infixl 4 .|.
(.|.) = for
infixl 6 .->.
(.->.) = fimplies

embedF :: FormulaF PropF (Formula r a) -> Formula r a
embedF (AndF x y) = fand x y
embedF (OrF x y) = for x y
embedF (ImpliesF x y) = fimplies x y
embedF (NotF x) = fnot x
embedF Truth = ftruth
embedF Falsehood = ffalsehood
embedF (ModalityF m) = absurd (getConst m)

embed :: Functor m => PropFormula a -> Formula m a
embed = iterM embedF

