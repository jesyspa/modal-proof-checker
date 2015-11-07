module Checker.PrettyPrint where

import Checker.Formula
import Checker.Modal
import Checker.Proof
import Text.PrettyPrint
import Control.Monad.Free
import Data.Void
import Control.Applicative

type PrecDoc = Int -> Doc

parensAt :: Int -> PrecDoc -> PrecDoc
parensAt m x n | m < n = parens (x 0)
               | otherwise = x m

-- Precedence:
-- box, diamond, negation bind tightest (3)
-- and is next (2)
-- then or (1)
-- then implies (0)

ppFormulaF :: Functor m => (m PrecDoc -> PrecDoc) -> FormulaF m PrecDoc -> PrecDoc
ppFormulaF _ (AndF x y) = parensAt 2 $ \n -> x n <+> text "&" <+> y n
ppFormulaF _ (OrF x y) = parensAt 1 $ \n -> x n <+> text "|" <+> y n
ppFormulaF _ (ImpliesF x y) = parensAt 0 $ \n -> x (n+1) <+> text "->" <+> y n
ppFormulaF _ (NotF x) = parensAt 3 $ \n -> text "¬" <> x n
ppFormulaF f (ModalityF m) = f m

ppModalF :: ModalF PrecDoc -> PrecDoc
ppModalF (BoxF x) = parensAt 3 $ \n -> text "☐" <> x n
ppModalF (DiamondF x) = parensAt 3 $ \n -> text "◇" <> x n

ppFormula' :: Functor m => (m PrecDoc -> PrecDoc) -> Formula m PrecDoc -> PrecDoc
ppFormula' f = iter (ppFormulaF f)

ppFormula :: Functor m => (m PrecDoc -> PrecDoc) -> Formula m Doc -> Doc
ppFormula f = ($0) . ppFormula' f . fmap const

ppModalFormula :: ModalFormula Doc -> Doc
ppModalFormula = ppFormula ppModalF

ppRuleApplication :: RuleApplication Doc -> Doc
ppRuleApplication (Tautology pf)      = ppFormula (absurd . getConst) pf
ppRuleApplication (Substitution mf s) = ppModalFormula (mf >>= toFun s return) <+> parens (text "from" <+> ppModalFormula mf <+> text "by substitution")
ppRuleApplication (K x y)             = ppModalFormula (fk x y) <+> parens (text "K axiom")
ppRuleApplication (DualL x)           = ppModalFormula (fduall x) <+> parens (text "Dual axiom")
ppRuleApplication (DualR x)           = ppModalFormula (fdualr x) <+> parens (text "Dual axiom")
ppRuleApplication (ModusPonens ma ms) = ppModalFormula ms <+> parens reason
    where reason = text "from" <+> ppModalFormula ma <+> text "and" <+> ppModalFormula (ma .->. ms) <+> text "by modus ponens"
ppRuleApplication (Generalize mf)     = ppModalFormula (fbox mf) <+> parens (text "from" <+> ppModalFormula mf)

ppProof :: Proof Doc -> Doc
ppProof = vcat . map ppRuleApplication

printProof :: Proof String -> String
printProof = render . ppProof . map (fmap text)
