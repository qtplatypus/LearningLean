import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Test.Libary.Bijections
import Test.Libary.KTFP

-- Based on http://arg.ciirc.cvut.cz/fmpa/slides/cbs.pdf
-- however this proof either contains a few errors or I am missreading it.
-- Or both.  Other sources that I have used is nlab

-- https://ncatlab.org/nlab/show/Cantor-Schroeder-Bernstein+theorem
-- Hoever it has the wonderful "The rest is obvious". when it isn't
-- at all.

-- A better source of proof would be delightful.
open Set

-- A proof of the Cantor–Schröder–Bernstein theorem

-- Basically if we have an injection A → B and and injection B → A then we have a
-- Bijection A ↔ B+

theorem CBS {A : Type} {B : Type} : hasInjection (A) (B) ∧ hasInjection (B) (A)
  → hasBijection (A) (B) := by {

  -- Broadly the stratagy here is to use KnasterTarskiFixedPoint theorm
  -- to create a subset of A.

  -- Our main vars

  -- f  : A → B is the forward injective function
  -- fi : B → A is f's inverse
  -- ab_inj : fi ∘ f = id is the proof that they are injective
  -- g, gi and ba_inj are the equiverlent with A and B swapped.
  intro ⟨ ⟨ f , ⟨ fi , ab_inj⟩ ⟩, ⟨ g, ⟨ gi , ba_inj⟩ ⟩ ⟩

  -- here is phi our monotone function.
  let φ := fun X: Set A ↦ (g '' (f '' X)ᶜ)ᶜ

  -- Prove that phi is monotone
  let monophi : monotone A A φ := by {
    intro U V UsubV

    have h2 : f '' U ⊆ f '' V := image_mono UsubV
    rw [← Set.compl_subset_compl] at h2

    have h3 : g '' (f '' V)ᶜ ⊆ g '' (f '' U)ᶜ := image_mono h2
    rw [← Set.compl_subset_compl] at h3
    exact h3
  }

  -- C is a fixed point of φ and CisFixed is the
  -- witness to the fact that this point is fixed under phi.
  obtain ⟨ C, CisFixed ⟩ := KnasterTarskiFixedPoint monophi

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

  -- The forward bijective function from A to B
  let forward (x : A) : B :=
    -- There is an interesting conversation about how constructive this
    -- proof is.  While it clearly works for finite cases and infinite classical
    -- sets.  In a broader sense there are places where it breaks down.
    open Classical in

    if hx : x ∈ C
      then f x   -- Maps elements from C to f '' C (a subset of B)
      else gi x  -- Maps elements from Cᶜ to (f '' C)ᶜ

  let backward (b : B) : A :=
    open Classical in

    if hy : b ∈ (f '' C)
      then fi b -- Maps elements from f '' C  to C  (a subset of A)
      else g b  -- Maps elements from (f '' C)ᶜ to C

  have left_inverse_witness : forward ∘ backward = id := by {
    funext z
    by_cases hz : z ∈ (f '' C)

    case pos =>
      unfold backward
      simp only [Function.comp_apply, hz]
      unfold forward
      rw [mem_image] at hz
      obtain ⟨ a , haC⟩ := hz
      have hfi := congrFun ab_inj a
      rw [Function.comp] at hfi
      by_cases hy : fi z ∈ C

      case pos =>
        simp only [hy, ↓reduceDIte]
        rw [← haC.right]
        simp only [hfi, id_eq]
      case neg =>
        rw [← haC.right] at hy
        simp only [hfi, id_eq] at hy
        exact False.elim (hy haC.left)

    case neg =>
      unfold backward
      simp only [Function.comp_apply, hz, id_eq]
      unfold forward
      by_cases hy : g z ∈ C

      case pos =>
        rw [← mem_compl_iff] at hz
        have hgi := mem_image_of_mem g hz
        rw [two] at hy
        rw [mem_compl_iff] at hy
        exact False.elim (hy hgi)
      case neg =>
        simp only [hy, ↓reduceDIte]
        rw [cancelInverse g gi]
        rw [ba_inj]
  }

  have right_inverse_witness : backward ∘ forward = id := by {
    funext z
    by_cases hy : z ∈ C

    case pos =>
      unfold forward
      simp only [Function.comp_apply, hy, id_eq]
      unfold backward
      by_cases hx : f z ∈ (f '' C)

      case pos =>
        simp only [hx, ↓reduceDIte]
        rw [cancelInverse f fi]
        exact ab_inj
      case neg =>
        have hgi := mem_image_of_mem f hy
        exact False.elim (hx hgi)


    case neg =>
      unfold backward
      dsimp
      by_cases hx : (forward z) ∈ (f '' C)

      case pos =>
        -- this can't be reached so prove it
        -- false just like above
        unfold forward at hx
        simp only [hy] at hx
        rw [two] at hy
        rw [mem_compl_iff, not_not] at hy
        have gihy := mem_image_of_mem gi hy
        rw [image_reverse_comp] at gihy
        exact False.elim (gihy hx)
        exact ba_inj
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
        simp only [hx]
        unfold forward
        simp only [hy]

        -- I am curious about this.
        -- we are not in a classical
        -- namesapce but clearly not_not
        -- is classical.  By using classical
        -- to define backwards and forwards
        -- does lean work out that I am ment to be classical
        -- here?

        rw [two, mem_compl_iff, not_not, mem_image] at hy

        obtain ⟨ x , hhx ⟩ := hy
        have deco := congrArg gi hhx.right
        rw [cancelInverse g gi] at deco
        rw [← deco]
        exact hhx.right
        exact ba_inj
  }

  use forward
  use backward
}
