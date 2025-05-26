import Catenary.RelSeriesHT.Codim
import Catenary.Order.Defs
import Mathlib.RingTheory.Spectrum.Prime.Basic

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
  sorry

lemma field_isCatenaryRing (F : Type*) [Field F]: IsCatenaryRing F := by
  have h : Subsingleton (PrimeSpectrum F) := by
    infer_instance
  unfold IsCatenaryRing
  sorry
