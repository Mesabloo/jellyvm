{-# LANGUAGE UnicodeSyntax, RankNTypes, GADTs, NoImplicitPrelude #-}

module LAM.LAM where

import LL.Types (Combinator((:<>)), Combinator((:<)), Combinator((:⌷)), Combinator((:⎨)), Combinator((:∘)), Combinator((:×)), Value((:⌟)), Value((:·)))
import qualified LL.Types as LL
import LAM.Types
import Prelude (($), (.), error)
import Debug.Trace (traceShow)

linear :: forall a b d. LL.Combinator a b → Code Instruction a b d d
linear LL.Id = Empty
linear (y :∘ x) = linear x +. linear y
linear LL.Eone = Empty
linear (x :× y) = Pushl `Cons` (linear x +. (Consl `Cons` (Pushr `Cons` (linear y +. list Consr))))
linear LL.Ol = list Ol
linear LL.Cl = list Cl
linear LL.Or = list Or
linear LL.Cr = list Cr
linear LL.Ex = list Ex
linear LL.Al = list Al
linear LL.Ar = list Ar
linear (:<>) = list $ Constr (:<>)
linear (x :< y) = list $ Constr (x :< y)
linear LL.Fst = list Fst
linear LL.Snd = list Snd
linear (:⌷) = list Ø
linear LL.Inl = list $ Constr LL.Inl
linear LL.Inr = list $ Constr LL.Inr
linear (x :⎨ y) = list $ Altv (linear x) (linear y)
linear (LL.Lcur x) = list $ Constr (LL.Lcur x)
linear LL.Lapp = list Lapp
linear (LL.Make x y z) =  list $ Constr (LL.Make x y z)
linear LL.Read = list Read
linear LL.Kill = list Kill
linear LL.Dupl = list Dupl
linear LL.Zero' = list $ Constr LL.Zero'
linear LL.Succ = list $ Constr LL.Succ
linear (LL.Nrec x y) = list $ Nrec (linear x) (linear y)

run :: forall a b d e. Code Instruction a b d e → LL.Value a → Dump d → LL.Value b
run (Pushl `Cons` c) (u :⌟ v) d = run c u (v `Push` d)
run (Consl `Cons` c) u (v `Push` d) = run c (u :⌟ v) d
run (Pushr `Cons` c) (u :⌟ v) d = run c v (u `Push` d)
run (Consr `Cons` c) v (u `Push` d) = run c (u :⌟ v) d
run (Ol `Cons` c) u d = run c (LL.Unit :⌟ u) d
run (Cl `Cons` c) (LL.Unit :⌟ u) d = run c u d
run (Or `Cons` c) u d = run c (u :⌟ LL.Unit) d
run (Cr `Cons` c) (u :⌟ LL.Unit) d = run c u d
run (Ex `Cons` c) (u :⌟ v) d = run c (v :⌟ u) d
run (Al `Cons` c) (u :⌟ (v :⌟ w)) d = run c ((u :⌟ v) :⌟ w) d
run (Ar `Cons` c) ((u :⌟ v) :⌟ w) d = run c (u :⌟ (v :⌟ w)) d
run (Constr γ `Cons` c) u d = run c (γ :· u) d
run (Fst `Cons` c) ((c' :< c'') :· u) d = run (linear c'  +. c) u d
run (Snd `Cons` c) ((c' :< c'') :· u) d = run (linear c'' +. c) u d
run (Altv c' c'' `Cons` c) (LL.Inl :· u) d = run (c'  +. c) u d
run (Altv c' c'' `Cons` c) (LL.Inr :· u) d = run (c'' +. c) u d
run (Lapp `Cons` c) ((LL.Lcur c' :· u) :⌟ v) d = run (linear c' +. c) (u :⌟ v) d
run (Read `Cons` c) (LL.Make x y z :· u) d = run (linear x +. c) u d
run (Kill `Cons` c) (LL.Make x y z :· u) d = run (linear y +. c) u d
run (Dupl `Cons` c) (LL.Make x y z :· u) d = run (linear z +. linear (LL.Make x y z :× LL.Make x y z) +. c) u d
run (Nrec x y `Cons` c) (LL.Zero' :· y0) d = run (x +. c) LL.Unit d
run (Nrec x y `Cons` c) (LL.Succ :· n) d = run ((Nrec x y `Cons` y) +. c) n d
run Empty u Null = u
run Empty u (d' `Push` d) = u -- Should we never happening as the dump should be empty
run c v d = traceShow c . traceShow v . traceShow d $ error "Unreachable pattern reached!"