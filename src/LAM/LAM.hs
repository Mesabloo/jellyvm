{-# LANGUAGE UnicodeSyntax, RankNTypes, GADTs, NoImplicitPrelude #-}

module LAM.LAM where

import qualified LL.Types as LL
import LAM.Types
import Prelude (($), (.), error)
import Debug.Trace (traceShow)

linear :: forall a b d. LL.Combinator a b → Code Instruction a b d d
linear LL.Id = Empty
linear (y LL.:∘ x) = linear x +. linear y
linear LL.Eone = Empty
linear (x LL.:× y) = Pushl `Cons` (linear x +. (Consl `Cons` (Pushr `Cons` (linear y +. list Consr))))
linear LL.Ol = list Ol
linear LL.Cl = list Cl
linear LL.Or = list Or
linear LL.Cr = list Cr
linear LL.Ex = list Ex
linear LL.Al = list Al
linear LL.Ar = list Ar
linear (LL.:<>) = list $ Constr (LL.:<>)
linear (x LL.:< y) = list $ Constr (x LL.:< y)
linear LL.Fst = list Fst
linear LL.Snd = list Snd
linear (LL.:⌷) = list Ø
linear LL.Inl = list $ Constr LL.Inl
linear LL.Inr = list $ Constr LL.Inr
linear (x LL.:⎨ y) = list $ Altv (linear x) (linear y)
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
run (Pushl `Cons` c) (u LL.:⌟ v) d = run c u (v `Push` d)
run (Consl `Cons` c) u (v `Push` d) = run c (u LL.:⌟ v) d
run (Pushr `Cons` c) (u LL.:⌟ v) d = run c v (u `Push` d)
run (Consr `Cons` c) v (u `Push` d) = run c (u LL.:⌟ v) d
run (Ol `Cons` c) u d = run c (LL.Unit LL.:⌟ u) d
run (Cl `Cons` c) (LL.Unit LL.:⌟ u) d = run c u d
run (Or `Cons` c) u d = run c (u LL.:⌟ LL.Unit) d
run (Cr `Cons` c) (u LL.:⌟ LL.Unit) d = run c u d
run (Ex `Cons` c) (u LL.:⌟ v) d = run c (v LL.:⌟ u) d
run (Al `Cons` c) (u LL.:⌟ (v LL.:⌟ w)) d = run c ((u LL.:⌟ v) LL.:⌟ w) d
run (Ar `Cons` c) ((u LL.:⌟ v) LL.:⌟ w) d = run c (u LL.:⌟ (v LL.:⌟ w)) d
run (Constr γ `Cons` c) u d = run c (γ LL.:· u) d
run (Fst `Cons` c) ((c' LL.:< c'') LL.:· u) d = run (linear c'  +. c) u d
run (Snd `Cons` c) ((c' LL.:< c'') LL.:· u) d = run (linear c'' +. c) u d
run (Altv c' c'' `Cons` c) (LL.Inl LL.:· u) d = run (c'  +. c) u d
run (Altv c' c'' `Cons` c) (LL.Inr LL.:· u) d = run (c'' +. c) u d
run (Lapp `Cons` c) ((LL.Lcur c' LL.:· u) LL.:⌟ v) d = run (linear c' +. c) (u LL.:⌟ v) d
run (Read `Cons` c) (LL.Make x y z LL.:· u) d = run (linear x +. c) u d
run (Kill `Cons` c) (LL.Make x y z LL.:· u) d = run (linear y +. c) u d
run (Dupl `Cons` c) (LL.Make x y z LL.:· u) d = run (linear z +. linear (LL.Make x y z LL.:× LL.Make x y z) +. c) u d
run (Nrec x y `Cons` c) (LL.Zero' LL.:· y0) d = run (x +. c) LL.Unit d
run (Nrec x y `Cons` c) (LL.Succ LL.:· n) d = run ((Nrec x y `Cons` y) +. c) n d
run Empty u Null = u
run Empty u (d' `Push` d) = u -- Should we never happening as the dump should be empty
run c v d = traceShow c . traceShow v . traceShow d $ error "Unreachable pattern reached!"