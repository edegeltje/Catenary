import Catenary.RelSeriesHT.Codim
import Catenary.Order.Defs
import Mathlib.RingTheory.Spectrum.Prime.Basic
open scoped RelSeriesHT

variable (R : Type*) [CommSemiring R]

abbrev IsCatenaryRing : Prop := IsCatenaryOrder (PrimeSpectrum R)

instance subsingletonPreorder (S : Type*)[Subsingleton S]: Preorder S where
  le := λ _ _ ↦ True
  le_refl := by intros; trivial
  le_trans := by intros; trivial

lemma subsingleton_isCatenaryOrder (S : Type*) [Subsingleton S]: IsCatenaryOrder S := by
  constructor
  intros a b
  have h' : a = b := Subsingleton.elim a b
  rw[h']
  use 0
  simp only [RelSeriesHT.isReduced_of_irrefl, true_and]
  have h₃: ∀ x: b -[LT.lt]→* b, x.length = 0 := by
    intro x
    have h₆ : x = RelSeriesHT.singleton b := isSingleton_if x
    have h₄: x.length = 0 := by
      rw[h₆]
      simp only [RelSeriesHT.reduce_singleton, RelSeriesHT.length_singleton]
    rw[h₄]
  refine fun x ↦ by
    use x
    constructor
    · rfl
    · apply h₃

lemma field_isCatenaryRing (F : Type*) [Field F]: IsCatenaryRing F := by
  unfold IsCatenaryRing
  have h : Subsingleton (PrimeSpectrum F) := by
   infer_instance
  apply subsingleton_isCatenaryOrder at h
  sorry
