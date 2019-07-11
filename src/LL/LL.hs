{-# LANGUAGE UnicodeSyntax, NoImplicitPrelude, ExistentialQuantification, KindSignatures, DataKinds, GADTs, TypeOperators #-}

module LL.LL where

import Prelude (($), (.), error)
import Debug.Trace (traceShow)
import LL.Types

app :: ∀ (a :: Term) (b :: Term). a ⟶ b → Value a → Value b
app Id u = u
app (x :∘ y) u = app x (app y u)
app Eone Unit = Unit
app (phi :× psi) (x :⌟ y) = app phi x :⌟ app psi y
app Ol u = Unit :⌟ u
app Cl (Unit :⌟ u) = u
app Or u = u :⌟ Unit
app Cr (u :⌟ Unit) = u
app Ex (u :⌟ v) = v :⌟ u
app Al (u :⌟ (v :⌟ w)) = (u :⌟ v) :⌟ w
app Ar ((u :⌟ v) :⌟ w) = u :⌟ (v :⌟ w)
app (:<>) u = (:<>) :· u
app (x :< y) u = (x :< y) :· u
app Fst ((phi :< psi) :· u) = app phi u
app Snd ((phi :< psi) :· u) = app psi u
app Inl u = Inl :· u
app Inr u = Inr :· u
app (x :⎨ y) (Inl :· u) = app x u
app (x :⎨ y) (Inr :· u) = app y u
app (Lcur x) u = Lcur x :· u
app Lapp ((Lcur phi :· u) :⌟ v) = app phi (u :⌟ v)
app (Make x y z) u = Make x y z :· u
app Read (Make x y z :· u) = app x u
app Kill (Make x y z :· u) = app y u
app Dupl (Make x y z :· u) = app (Make x y z :× Make x y z) (app z u)
app Zero' Unit = Zero' :· Unit
app Succ u = Succ :· u
app (Nrec x y) (Zero' :· y1) = app x Unit
app (Nrec x y) (Succ :· y1) = app y (app (Nrec x y) y1)
app comb val = traceShow comb . traceShow val $ error "Forbidden pattern reached!"

hToLL :: HTerm → Term
hToLL HTrue = (:⊤)
hToLL HFalse = Zero
hToLL (x :∧ y) = hToLL x :& hToLL y
hToLL (x :∨ y) = (:!) (hToLL x) :⊕ (:!) (hToLL y)
hToLL (x :⇒ y) = (:!) (hToLL x) :⊸ hToLL y