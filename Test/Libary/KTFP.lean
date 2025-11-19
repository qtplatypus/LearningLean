import Mathlib.Tactic
import Mathlib.Data.Set.Basic

-- Based on http://arg.ciirc.cvut.cz/fmpa/slides/cbs.pdf

-- This is a proof of KnasterTarskiFixedPoint theorem on the powerset of a set with
-- the order operator being the subset function.
open Set

def monotone (A B) (φ : Set A → Set B)
  := ∀ U : Set A, ∀ V : Set A, U ⊆ V → φ U ⊆ φ V

def antimonotone (A B) (φ : Set A → Set B)
  := ∀ U : Set A, ∀ V : Set A, U ⊆ V → φ V ⊆ φ U

-- complement_antimonotone. A compliment is always antimonotone.
-- U ⊆ V → Vᶜ ⊆ Uᶜ .
lemma complement_antimonotone A : antimonotone A A (fun X ↦ Xᶜ) := by {
    intro _ _ UsubV _ aInComp aInU

    exact aInComp (UsubV aInU)
}

-- image_monotone. A function that is an image is always monotone
-- U ⊆ V → f''U ⊆ f''V
-- The image of V is going to be all the elements in the image of U (because U is a subset of V).
-- pluss the images of anything that is in V / U
lemma image_mono A B (f : A → B) : monotone A B (fun X ↦ f '' X) := by {
  intro _ V UsubV b ⟨ x1, hx1⟩

  refine (mem_image f V b).mpr ?_

  use x1

  apply And.intro
  case left =>
    exact UsubV hx1.left

  case right =>
    exact hx1.right
}

-- KnasterTarskiFixedPoint. If there is a monotonal endofunction on Set A then there are
-- fixed points.
theorem KnasterTarskiFixedPoint A (φ : Set A → Set A) : monotone A A φ →
  ∃ Y : Set A, φ Y = Y := by {
    intro a

    -- Y is the set of all fixed points.
    let Y := { a : A | ∀ X : Set A, φ X ⊆ X → a ∈ X }
    use Y

    -- At this point we have to prove that Y is the set of all fixed points.  IE φ Y = Y.

    -- Lemma One from the document.  A better name for this would
    -- be helpful
    have one : ∀ X : Set A, φ X ⊆ X → Y ⊆ X := by {
      intro X1 phiX1subX1 _ aInY

      exact aInY X1 phiX1subX1
    }

    -- Prove that φ Y ⊆ Y the first step in proving φ Y = Y
    have mp : φ Y ⊆ Y := by {
      intro _ aInPhiV X PhiXSubsetX

      exact PhiXSubsetX ((a Y X (one X PhiXSubsetX)) aInPhiV)
    }

    -- Prove that Y ⊆ φ Y the second step in proving φ Y = Y
    have mpr : Y ⊆ φ Y := by {
      exact one (φ Y) (a (φ Y) Y mp)
    }

    apply Set.Subset.antisymm
    · exact mp
    · exact mpr
}
