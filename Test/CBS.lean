import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Test.Libary.Bijections
import Test.Libary.KTFP


-- WIP this is broken and I'm only uploading
-- this for advice and help.  Don't use this
-- I'm a beginner at LEAN and this most likely
-- has massive style and coding problems.

-- Esp since at a number of key places i've used sorry.

-- Based on http://arg.ciirc.cvut.cz/fmpa/slides/cbs.pdf
-- however this proof either contains a few errors or I am missreading it.
-- Or both.  Other sources that I have used is nlab

-- https://ncatlab.org/nlab/show/Cantor-Schroeder-Bernstein+theorem
-- Hoever it has the wonderful "The rest is obvious". when it isn't
-- at all.

-- A better source of proof would be delightful.

-- Part of the problem with me doing this is because I'm using my own definitions
-- of bijective and injective but also I suspect it is because I don't know all
-- the theorems that lean gives me.  Also I just might not be understanding
-- enough about he proof to formalise it.

open Set

-- More debugging infomation
set_option diagnostics true


-- This was a little helper lemma but I'm not sure that it is needed and might
-- have been the result of me following down wrong paths.

lemma antisym_for_subtypes (PP) (p)
  (P : {_x : Set PP // p }) (Q : {_x : Set PP // p }) (l : P.val ⊆ Q.val) (r : Q.val ⊆ P.val) :
  (P = Q) := by {
    ext x

    apply Iff.intro
    case a.h.mp =>
      intro xInP
      have xInQ := l xInP
      exact xInQ
    case a.h.mpr =>
      intro xInQ
      have xInP := r xInQ
      exact xInP
}

-- A proof of the Cantor–Schröder–Bernstein theorem

-- Basically if we have an injection A → B and and injection B → A then we have a
-- Bijection A ↔ B+

theorem CBS (A : Type) (B : Type) : hasInjection (A) (B) ∧ hasInjection (B) (A) → hasBijection (A) (B) := by {

  -- Our main vars

  -- f  : A → B is the forward injective function
  -- fi : B → A is f's inverse
  -- ab_inj : fi ∘ f = id is the proof that they are injective

  -- g, gi and ba_inj are the equiverlent with A and B swapped.
  intro ⟨ ⟨ f , ⟨ fi , ab_inj⟩ ⟩, ⟨ g, ⟨ gi , ba_inj⟩ ⟩ ⟩

  -- here is phi our monotone function.  However
  -- I'm not sure that we have defined it correctly for
  -- what we are doing.  Diffrent souces seem to have.
  -- it as (g '' (f '' X)ᶜ)ᶜ and (g '' (f '' Xᶜ)ᶜ)
  -- And I'm unsure which is correct or even if it matters.

  let φ := fun X: Set A ↦ (g '' (f '' X)ᶜ)ᶜ

  -- Prove that phi is monotone
  let monophi : monotone A A φ := by {
    open Classical in
    intro U V UsubV

    have h2 : f '' U ⊆ f '' V := image_mono UsubV
    rw [← Set.compl_subset_compl] at h2

    have h3 : g '' (f '' V)ᶜ ⊆ g '' (f '' U)ᶜ := image_mono h2
    rw [← Set.compl_subset_compl] at h3
    exact h3
  }

  -- C is a fixed point of φ and CisFixed is the
  -- witness to the fact that this point is fixed.
  obtain ⟨ C, CisFixed ⟩ := KnasterTarskiFixedPoint A φ monophi

  -- TODO: This needs a better name.
  -- This is equasion (2) from the pdf

  let two ( x ) : x ∈ C ↔ x ∈ (g '' (f '' C)ᶜ)ᶜ := by {
    apply Iff.intro

    case mp =>
      intro xInC
      rw [← CisFixed] at xInC
      exact xInC

    case mpr =>
      intro xpC
      rw [← CisFixed]
      exact xpC
  }

  -- Some helper functions.  I'm not sure if these are needed anymore.
  have inverseIsUnique_f (y z a)  ( forwardEQ : a = f y ) ( backwardEQ : fi a = z): y = z :=
    inverseIsUnique A B f fi ab_inj y z a forwardEQ backwardEQ

  have inverseIsUnique_g (y z a) ( forwardEQ : a = g y) (backwardEQ : gi a = z ) : y = z :=
    inverseIsUnique B A g gi ba_inj y z a forwardEQ backwardEQ

  -- TODO : refactor these.  My injective witness is in the form of fi ∘ f = id and this
  -- allows me to do  f x1 = z ∧ f x2 = z -> x1 = x2.  I am now aware that this
  -- is something that is in lean's standard libaries.

  have use_injection_f (x1 x2 z) : f x1 = z ∧ f x2 = z → x1 = x2 := by {
    intro ⟨ fleft, fright ⟩
    rw [← fright] at fleft

    have ff := congrArg fi fleft

    have cfx1 : (fi ∘ f) x1 = id x1 := by {exact congrFun ab_inj x1}
    rw [Function.comp_apply] at cfx1
    rw [cfx1] at ff

    have cfx2 : (fi ∘ f) x2 = id x2 := by {exact congrFun ab_inj x2}
    rw [Function.comp_apply] at cfx2
    rw [cfx2] at ff

    exact ff
  }

  have use_injection_g (x1 x2 z) : g x1 = z ∧ g x2 = z → x1 = x2 := by {
    intro ⟨ gleft, gright ⟩
    rw [← gright] at gleft

    have gf := congrArg gi gleft

    have cgx1 : (gi ∘ g) x1 = id x1 := by {exact congrFun ba_inj x1}
    rw [Function.comp_apply] at cgx1
    rw [cgx1] at gf

    have cgx2 : (gi ∘ g) x2 = id x2 := by {exact congrFun ba_inj x2}
    rw [Function.comp_apply] at cgx2
    rw [cgx2] at gf

    exact gf
  }

  -- Another bit of refactoring should be done here.  This
  -- is to transform (fi '' (f '' x)) into x.  Again there is
  -- a standard libary function for this but I discovered it
  -- long after I had started down this path.

  have image_reverse_comp_f (a : Set A) : (fi '' (f '' a) = a) := by {
    ext
    apply Iff.intro
    case mp =>
      intro h
      rw [← image_id a]
      rw [← ab_inj]
      rw [image_comp]
      exact h
    case mpr =>
      intro h
      rw [← image_id a] at h
      rw [← ab_inj] at h
      rw [image_comp] at h
      exact h
  }

  have image_reverse_comp_g (a : Set B) : (gi '' (g '' a) = a) := by {
    ext
    apply Iff.intro
    case mp =>
      intro h
      rw [← image_id a]
      rw [← ba_inj]
      rw [image_comp]
      exact h
    case mpr =>
      intro h
      rw [← image_id a] at h
      rw [← ba_inj] at h
      rw [image_comp] at h
      exact h
  }

  -- Restrictions on A and B so that they are inside the
  -- fixed point set.  The goal of these was to allow
  -- me to carry the infomation about the fact that f and fi
  -- are "closed" within this set and use it to prove that
  -- they are bijective.

  -- Hoever dealing with subtypes in lean is super complex
  -- and beyond my skill level.  Indeed I suspect that this
  -- is the wrong approch and I got here by following a xy issue
  -- where I am using the wrong tools.

  let A_res := { a : A // a ∈ C      }
  let B_res := { b : B // b ∈ f '' C }

  let f_res (x : A_res) : (B_res) := by {
    exact imageFactorization f C x
  }

  let fi_res (y : B_res) : (A_res) := by {
    have x := imageFactorization fi (f '' C) y
    simp [image_reverse_comp_f] at x
    exact x
  }

  let forward (x : A) : B :=
    open Classical in

    -- Is the extra subtype anotation a good idea or another mistake.

    if hx : x ∈ C
      then f x   -- Maps elements from C to f '' C (a subset of B)
      else gi x  -- Maps elements from Cᶜ to (f '' C)ᶜ  or is it (f '' Cᶜ)?

  let backward (b : B) : A :=
    open Classical in

    if hy : b ∈ (f '' C)
      then fi b -- Maps elements from f '' C  to C  (a subset of A)
      else g b  -- Maps elements from (f '' C)ᶜ to C


  -- This corrasponds to equasion 3 from the pdf.  However I thing what the author
  -- wrote was wrong?  Or whatever it was I couldn't prove it but I can prove this.
  have three x y (xnInC : x ∈ Cᶜ) (xEQgy : x = g y) : (y ∉ f '' C) := by {
    rw [mem_compl_iff] at xnInC
    rw [two] at xnInC
    rw [mem_compl_iff] at xnInC
    rw [not_not] at xnInC
    rw [xEQgy] at xnInC
    have deco := mem_image_of_mem gi xnInC
    rw [cancelInverse B A g gi] at deco
    rw [image_reverse_comp_g] at deco
    exact deco
    exact ba_inj
  }

  have left_inverse_witness : forward ∘ backward = id := by {
    funext z

    by_cases hy : z ∈ (f '' Cᶜ)ᶜ
    case pos =>
      sorry
    case neg =>
      sorry
  }

  have right_inverse_witness : backward ∘ forward = id := by {
    open Classical in
    funext z

    by_cases hy : z ∈ C
    case pos =>
      unfold forward
      simp [hy]
      unfold backward
      by_cases hx : f z ∈ (f '' C)
      case pos =>
        simp [hx]
        rw [cancelInverse A B f fi]
        exact ab_inj
      case neg =>
        -- this can't be reached so prove it
        -- false (use three here?) to create
        -- a contradiction
        sorry

    case neg =>
      unfold backward
      dsimp
      by_cases hx : (forward z) ∈ (f '' Cᶜ)ᶜ
      case pos =>
        -- this can't be reached so prove it
        -- false just like above

        simp only [forward] at hx
        simp only [hy] at hx
        dsimp at hx
        rw [← mem_compl_iff] at hy
        sorry

      case neg =>
        -- We now have as the goal
        -- g (gi z) = z
        -- for g : B → A
        -- We know that gi (g z) = x
        -- However (gi z) doesn't neccarrally
        -- work out.  Because if A was
        -- larger then B.  The gi would not be
        -- injective.  So we have to prove that
        -- it is.
        unfold forward
        simp [hy]
        sorry
  }

  use forward
  use backward
}
