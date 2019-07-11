{-# LANGUAGE UnicodeSyntax, NoImplicitPrelude, ExistentialQuantification, KindSignatures, DataKinds, GADTs, TypeOperators #-}

module LL.Types where

import Prelude (Show(..), (<>), undefined)

data HTerm
    = HTrue          -- ^ True
    | HFalse         -- ^ False
    | HTerm :∧ HTerm -- ^ And
    | HTerm :∨ HTerm -- ^ Or
    | HTerm :⇒ HTerm -- ^ Implication

data Term
    = One          -- ^ ~ ()
    | Zero         -- ^ ~ Void
    | (:⊤)         -- ^ True
    | (:⊥)         -- ^ Multiplicative falsity
    | Term :⊗ Term -- ^ Eager pair
    | Term :⊕ Term -- ^ Either
    | Term :& Term -- ^ Lazy pair
    | (:!) Term    -- ^ Non linear
    | Term :⊸ Term -- ^ Linear arrow 
    | Nat          -- ^ Natural number

data Combinator :: Term → Term → * where -- ^ Denotated as `Term ⟶ Term`
    Id    :: ∀ a.       Combinator a a
    (:∘)  :: ∀ a b c.   Combinator b c → Combinator a b → Combinator a c
    Eone  ::            Combinator 'One 'One
    (:×)  :: ∀ a b c d. Combinator a b → Combinator c d → Combinator (a ':⊗ c) (b ':⊗ d)
    Ol    :: ∀ a.       Combinator a ('One ':⊗ a) 
    Cl    :: ∀ a.       Combinator ('One ':⊗ a) a 
    Or    :: ∀ a.       Combinator a (a ':⊗ 'One)
    Cr    :: ∀ a.       Combinator (a ':⊗ 'One) a  
    Ex    :: ∀ a b.     Combinator (a ':⊗ b) (b ':⊗ a)  
    Al    :: ∀ a b c.   Combinator (a ':⊗ (b ':⊗ c)) ((a ':⊗ b) ':⊗ c) 
    Ar    :: ∀ a b c.   Combinator ((a ':⊗ b) ':⊗ c) (a ':⊗ (b ':⊗ c))  
    (:<>) :: ∀ x.       Combinator x '(:⊤) 
    (:<)  :: ∀ x a b.   Combinator x a → Combinator x b → Combinator x (a ':& b) 
    Inl   :: ∀ a b.     Combinator a (a ':⊕ b) 
    Inr   :: ∀ a b.     Combinator b (a ':⊕ b)
    Lcur  :: ∀ x a b.   Combinator (x ':⊗ a) b → Combinator x (a ':⊸ b) 
    Make  :: ∀ x a.     Combinator x a → Combinator x 'One → Combinator x (x ':⊗ x) → Combinator x ('(:!) a) 
    Fst   :: ∀ a b.     Combinator (a ':& b) a 
    Snd   :: ∀ a b.     Combinator (a ':& b) b
    (:⌷)  :: ∀ x.       Combinator 'Zero x
    (:⎨)  :: ∀ a b x.   Combinator a x → Combinator b x → Combinator (a ':⊕ b) x
    Lapp  :: ∀ a b.     Combinator ((a ':⊸ b) ':⊗ a) b 
    Read  :: ∀ a.       Combinator ('(:!) a) a 
    Kill  :: ∀ a.       Combinator ('(:!) a) 'One
    Dupl  :: ∀ a.       Combinator ('(:!) a) ('(:!) a ':⊗ '(:!) a) 
    Zero' ::            Combinator 'One 'Nat
    Succ  ::            Combinator 'Nat 'Nat
    Nrec  :: ∀ x.       Combinator 'One x → Combinator x x → Combinator 'Nat x

type (⟶) = Combinator

data Value :: Term → * where
    Unit ::         Value 'One
    (:⌟) :: ∀ a b. Value a → Value b → Value (a ':⊗ b)
    (:·) :: ∀ a b. (a ⟶ b) → Value a → Value b

------------------------------------------------------------------------------------------------------------------

instance Show HTerm where
    show HTrue = "True"
    show HFalse = "False"
    show (h1 :∧ h2) = "(" <> show h1 <> " ∧ " <> show h2 <> ")"
    show (h1 :∨ h2) = "(" <> show h1 <> " ∨ " <> show h2 <> ")"
    show (h1 :⇒ h2) = "(" <> show h1 <> " ⇒ " <> show h2 <> ")"

instance Show Term where
    show One = "one"
    show Zero = "zero"
    show Nat = "ℕ"
    show (:⊤) = "⊤"
    show (:⊥) = "⊥"
    show (t1 :⊗ t2) = "(" <> show t1 <> " ⊗ " <> show t2 <> ")"
    show (t1 :⊕ t2) = "(" <> show t1 <> " ⊕ " <> show t2 <> ")"
    show (t1 :& t2) = "(" <> show t1 <> " & " <> show t2 <> ")"
    show ((:!) t1) = "!" <> show t1
    show (t1 :⊸ t2) = "(" <> show t1 <> " ⊸ " <> show t2 <> ")"

instance ∀ a b. Show (Combinator a b) where
    show Id = "(a ⟶ a)"
    show Eone = "(" <> show One <> " ⟶ one)"
    show Ol = "(a ⟶ " <> show One <> " ⊗ a)"
    show Cl = "(" <> show One <> " ⊗ a ⟶ a)"
    show Or = "(a ⟶ a ⊗ " <> show One <> ")"
    show Cr = "(a ⊗ " <> show One <> " ⟶ a)"
    show Ex = "(a ⊗ b ⟶ b ⊗ a)"
    show Al = "(a ⊗ (b ⊗ c) ⟶ (a ⊗ b) ⊗ c)"
    show Ar = "((a ⊗ b) ⊗ c ⟶ a ⊗ (b ⊗ c))"
    show Inl = "(a ⟶ a ⊕ b)"
    show Inr = "(b ⟶ a ⊕ b)"
    show Fst = "(a ⊗ b ⟶ a)"
    show Snd = "(a ⊗ b ⟶ b)"
    show Lapp = "((a ⊸ b) ⊗ a ⟶ b)"
    show Read = "(!a ⟶ a)"
    show Kill = "(!a ⟶ " <> show One <> ")"
    show Dupl = "(!a ⟶ (!a ⊗ !a))"
    show Zero' = "(" <> show One <> " ⟶ " <> show Nat <> ")"
    show Succ = "(" <> show Nat <> " ⟶ " <> show Nat <> ")"
    show (Nrec c1 c2) = "(" <> show c1 <> " `nrec` " <> show c2 <> ")"
    show (Lcur c1) = "(lcur " <> show c1 <> ")"
    show (Make c1 c2 c3) = "(make " <> show c1 <> " " <> show c2 <> " " <> show c3 <> ")"
    show (c1 :∘ c2) = "(" <> show c1 <> " ∘ " <> show c2 <> ")"
    show (c1 :× c2) = "(" <> show c1 <> " × " <> show c2 <> ")"
    show (c1 :< c2) = "〈" <> show c1 <> ", " <> show c2 <> "〉"
    show (:<>) = show (:⊤)
    show (:⌷) = "(" <> show Zero <> " ⟶ x)"
    show (c1 :⎨ c2) = "[" <> show c1 <> ", " <> show c2 <> "]"

instance ∀ a. Show (Value a) where
    show Unit = "()"
    show (v1 :⌟ v2) = "(" <> show v1 <> ", " <> show v2 <> ")"
    show (c1 :· v2) = "(" <> show c1 <> " · " <> show v2 <> ")"