{-# LANGUAGE UnicodeSyntax, DataKinds, KindSignatures, GADTs, RankNTypes, NoImplicitPrelude, TypeOperators, ScopedTypeVariables, FlexibleInstances #-}

module LAM.Types where

import qualified LL.Types as LL
import Prelude(Show(..), String, (<>))

data Dump (d :: [LL.Term]) :: * where
    Null ::                          Dump '[]
    Push :: forall d (a :: LL.Term). LL.Value a → Dump d → Dump (a : d)

data Code (store :: LL.Term → LL.Term → [LL.Term] → [LL.Term] → *) :: LL.Term → LL.Term → [LL.Term] → [LL.Term] → * where
    Empty :: forall store a d.         Code store a a d d
    Cons  :: forall store a b c d e f. store a b d e → Code store b c e f → Code store a c d f

infixl 5 `Cons`

(+.) :: forall store a b c d e f. Code store a b d e → Code store b c e f → Code store a c d f
Empty    +. ys      = ys
(x `Cons` xs) +. ys = x `Cons` (xs +. ys)

list :: forall store a b d e. store a b d e → Code store a b d e
list a = a `Cons` Empty


data Instruction :: LL.Term → LL.Term → [LL.Term] → [LL.Term] → * where
    Pushl  :: forall d u v.   Instruction (u 'LL.:⊗ v) u d (v : d)
    Consl  :: forall d u v.   Instruction u (u 'LL.:⊗ v) (v : d) d
    Pushr  :: forall d u v.   Instruction (u 'LL.:⊗ v) v d (u : d)
    Consr  :: forall d u v.   Instruction v (u 'LL.:⊗ v) (u : d) d
    Ol     :: forall d u.     Instruction u ('LL.One 'LL.:⊗ u) d d
    Cl     :: forall d u.     Instruction ('LL.One 'LL.:⊗ u) u d d
    Or     :: forall d u.     Instruction u (u 'LL.:⊗ 'LL.One) d d
    Cr     :: forall d u.     Instruction (u 'LL.:⊗ 'LL.One) u d d
    Ex     :: forall d u v.   Instruction (u 'LL.:⊗ v) (v 'LL.:⊗ u) d d
    Al     :: forall d a b c. Instruction (a 'LL.:⊗ (b 'LL.:⊗ c)) ((a 'LL.:⊗ b) 'LL.:⊗ c) d d
    Ar     :: forall d a b c. Instruction ((a 'LL.:⊗ b) 'LL.:⊗ c) (a 'LL.:⊗ (b 'LL.:⊗ c)) d d
    Constr :: forall a b d.   (a `LL.Combinator` b) → Instruction a b d d
    Fst    :: forall d u v.   Instruction (u 'LL.:& v) u d d
    Snd    :: forall d u v.   Instruction (u 'LL.:& v) v d d
    Altv   :: forall d a b x. Code Instruction a x d d → Code Instruction b x d d → Instruction (a 'LL.:⊕ b) x d d
    Lapp   :: forall d a b.   Instruction ((a 'LL.:⊸ b) 'LL.:⊗ a) b d d
    Ø      :: forall d x.     Instruction 'LL.Zero x d d
    Read   :: forall d x.     Instruction ('(LL.:!) x) x d d
    Kill   :: forall d x.     Instruction ('(LL.:!) x) 'LL.One d d
    Dupl   :: forall d x.     Instruction ('(LL.:!) x) ('(LL.:!) x 'LL.:⊗ '(LL.:!) x) d d
    Nrec   :: forall d x.     Code Instruction 'LL.One x d d → Code Instruction x x d d → Instruction 'LL.Nat x d d

--------------------------------------------------------------------------------------------------------------------------

instance forall d. Show (Dump d) where
    show Null        = "[]"
    show (v `Push` d) = "[" <> show v <> show' d <> "]"
      where show' :: forall d. Dump d → String
            show' Null           = ""
            show' (v' `Push` d') = ", " <> show v' <> show' d'

instance forall a b c d. Show (Code Instruction a b c d) where
    show Empty        = "[]"
    show (v `Cons` c) = "[" <> show v <> show' c <> "]"
      where show' :: forall a b c d. Code Instruction a b c d → String
            show' Empty          = ""
            show' (v' `Cons` c') = ", " <> show v' <> show' c'

instance forall a b c d. Show (Instruction a b c d) where
    show Pushl = "Instr (u ⊗ v) u d (v : d)"
    show Consl = "Instr u (u ⊗ v) (v : d) d"
    show Pushr = "Instr (u ⊗ v) v d (u : d)"
    show Consr = "Instr v (u ⊗ v) (u : d) d"
    show Ol = "Instr u (" <> show LL.One <> " ⊗ u) d d"
    show Cl = "Instr (" <> show LL.One <> " ⊗ u) u d d"
    show Or = "Instr u (u ⊗ " <> show LL.One <> ") d d"
    show Cr = "Instr (u ⊗ " <> show LL.One <> ") u d d"
    show Ex = "Instr (u ⊗ v) (v ⊗ u) d d"
    show Al = "Instr (a ⊗ (b ⊗ c)) ((a ⊗ b) ⊗ c) d d"
    show Ar = "Instr ((a ⊗ b) 'LL.:⊗ c) (a 'LL.:⊗ (b 'LL.:⊗ c)) d d"
    show (Constr c1) = "(Constr " <> show c1 <> ")"
    show Fst = "Instr (u & v) u d d"
    show Snd = "Instr (u & v) v d d"
    show (Altv c1 c2) = "(Altv " <> show c1 <> " " <> show c2 <> ")"
    show Lapp = "Instr ((a ⊸ b) ⊗ a) b d d"
    show Ø = "Instr " <> show LL.Zero <> " x d d"
    show Read = "Instr (!x) x d d"
    show Kill = "Instr (!x) " <> show LL.One <> " d d"
    show Dupl = "Instr (!x) (!x ⊗ !x) d d"
    show (Nrec c1 c2) = "(Nrec " <> show c1 <> " " <> show c2 <> ")"