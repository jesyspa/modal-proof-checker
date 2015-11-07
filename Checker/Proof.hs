module Checker.Proof where

import Checker.Formula
import Checker.Modal
import Control.Monad.State
import Control.Monad.Except

data RuleApplication a = Tautology (PropFormula a)
                       | Substitution (ModalFormula a) [(a, ModalFormula a)]
                       | K a a
                       | DualL a
                       | DualR a
                       | ModusPonens (ModalFormula a) (ModalFormula a)
                       | Generalize (ModalFormula a)
                       deriving (Eq, Functor, Foldable, Traversable)
type Proof a = [RuleApplication a]

assert :: (MonadState [ModalFormula a] m, MonadError () m, Ord a) => Bool -> m ()
assert True = return ()
assert False = throwError ()

require :: (MonadState [ModalFormula a] m, MonadError () m, Ord a) => ModalFormula a -> m ()
require mf = do
    xs <- get
    assert $ mf `elem` xs

conclude :: (MonadState [ModalFormula a] m, MonadError () m, Ord a) => ModalFormula a -> m ()
conclude mf = modify (mf:)

checkStep :: (MonadState [ModalFormula a] m, MonadError () m, Ord a) => RuleApplication a -> m ()
checkStep (Tautology t) = assert $ isTautology t
checkStep (Substitution mf s) = do
    require mf
    conclude $ mf >>= toFun s return
checkStep (K x y) = conclude $ (fbox $ fvar x .->. fvar y) .->. ((fbox $ fvar x) .->. (fbox $ fvar y))
checkStep (DualL x) = conclude $ (fbox $ fvar x) .->. (fnot $ fdiamond $ fnot $ fvar x)
checkStep (DualR x) = conclude $ (fnot $ fdiamond $ fnot $ fvar x) .->. (fbox $ fvar x)
checkStep (ModusPonens ma ms) = do
    require ma
    require $ ma .->. ms
    conclude ms
checkStep (Generalize mf) = do
    require mf
    conclude $ fbox mf

checkProof :: Ord a => Proof a -> Bool
checkProof ps = case runExcept $ evalStateT (mapM_ checkStep ps) [] of
                        Left () -> False
                        Right () -> True

