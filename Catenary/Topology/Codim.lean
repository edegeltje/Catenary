import Catenary.RelSeriesHT.Defs
import Mathlib.Logic.Function.Defs
import Catenary.RelSeriesHT.Codim
import Mathlib.Topology.Sober
import Catenary.Order.Defs
import Mathlib.Data.Nat.Lattice

open TopologicalSpace Set.Notation RelSeriesHT Function

variable {X : Type*} [TopologicalSpace X] {U : Set X}

-- General results

lemma closure_irred_of_irred {U : Set X} (T : Set U) (T_irred : IsIrreducible T) :
    IsIrreducible (closure (X := X) T) :=
  by sorry

def irr_closed_restrict [TopologicalSpace X]{U : Set X} (Y : IrreducibleCloseds X) (hU : IsOpen U) (hi : (U ∩ Y).Nonempty): IrreducibleCloseds (U):=
    ⟨U ↓∩ Y,
      by
        have := Y.isIrreducible.isPreirreducible
        constructor
        · sorry
        rw [isPreirreducible_iff_isClosed_union_isClosed] at this ⊢
        intro z₁ z₂ hz₁ hz₂ hunion
        specialize this (closure z₁) (closure z₂) (isClosed_closure) isClosed_closure
        -- rw [← closure_union, ← Set.image_union] at this
        -- specialize this (exact?%)
        sorry
      , Y.isClosed.preimage_val⟩


-- This defines an order preservign map
def closure_irred {U : Set X} (U_open : IsOpen U) :
    RelIso (α := IrreducibleCloseds U)
           (β := {s : IrreducibleCloseds X // (U ∩ s).Nonempty})
           (· < ·) (· < ·) where
  toFun := fun T ↦
    ⟨⟨closure (X := X) T.carrier,
      closure_irred_of_irred T.carrier T.is_irreducible',
      isClosed_closure⟩, by
      obtain ⟨x, h⟩ := T.is_irreducible'.left
      use x
      sorry
    ⟩
  invFun Y := irr_closed_restrict Y U_open Y.prop
  left_inv      := sorry
  right_inv     := sorry
  map_rel_iff'  := sorry

lemma closure_strict_mono_on_irreducible_closed {U : Set X} {A B : IrreducibleCloseds U} (r : A < B) :
    (closure A.carrier) < (closure B) :=
  by sorry

-- Sup and bijection


lemma bijection_trans {A: Set X} {B: Set X} (T: A → B) (f: X → ℕ∞) (hf: ∀ a : A, f a = f (T a) ):
  f '' A = f '' ↑(T '' (Set.univ (α := A))) := by
  ext y
  constructor
  · rintro ⟨a, aA, yfa⟩
    let b:B:= T ⟨a, aA⟩
    use b
    constructor
    · simp
      use a, aA
    change f (↑(T ⟨a, aA⟩)) = y
    rw [←hf]
    rw [yfa]

  rintro ⟨b, bB, yfb⟩
  -- bB : b ∈ Subtype.val '' (T '' Set.univ)
  rcases bB with ⟨b_from_B, ⟨a_from_A, _h_a_in_univ, h_T_eq_b_from_B⟩, h_val_eq_b⟩
  rw [←h_val_eq_b] at yfb
  rw [← h_T_eq_b_from_B] at yfb
  rw [←hf] at yfb
  use a_from_A
  constructor
  · exact Subtype.coe_prop a_from_A
  exact yfb


lemma iSup_in_eq_sSup_image {A : Set X} (f : X → ℕ∞) :
    (⨆ x ∈ A, f x) = sSup (f '' A) := by
  rw [sSup_image]


lemma supremum_bijection_preserving {A : Set X} {B : Set X}
    (T : A → B) (f : X → ℕ∞) (hT : Bijective T) (hf : ∀ a : A, f a = f (T a)) :
      ⨆ (a ∈ A), f a  = ⨆ (b ∈ B), f b :=  by
  have h_from_bijection_trans : f '' A = f '' (Subtype.val '' (T '' (Set.univ : Set A))) :=
    bijection_trans T f hf
  rw [iSup_in_eq_sSup_image, iSup_in_eq_sSup_image]
  rw [bijection_trans T f hf]
  have h_inner_set_equality : Subtype.val '' (T '' (Set.univ : Set A)) = B := by
    rw [Set.image_univ]
    rw [(Function.Bijective.surjective hT).range_eq]
    exact Subtype.coe_image_univ B
  rw [h_inner_set_equality]


noncomputable def closure_of_irreducible_subset {U : Set X} (A : IrreducibleCloseds U) :
    IrreducibleCloseds X :=
  ⟨closure (A : Set U), sorry, by exact isClosed_closure⟩



-- Codimensions

noncomputable def codim [TopologicalSpace X] (Y : IrreducibleCloseds X) : WithBot ℕ∞ :=
  ⨆ (U : IrreducibleCloseds X), (eCodim Y U)

example (hU : IsOpen U) (a b : IrreducibleCloseds X) :
    (a -[(· < ·)]→* b) →
    ((closure_irred hU).invFun ⟨a, sorry⟩) -[(· < ·)]→* ((closure_irred hU).invFun ⟨b, sorry⟩) :=
  by sorry


-- this could be proven in a more general context of relations
lemma iso_length_preserving {U : Set X} (U_open : IsOpen U)
    (f:RelIso (α := IrreducibleCloseds U)
      (β := {s : IrreducibleCloseds X // (U ∩ s).Nonempty})
      (· < ·) (· < ·) ) (a b : IrreducibleCloseds U) (x : a -[(· < ·)]→* b ): x.reduce.length = (map f.toRelEmbedding.toRelHom x).reduce.length
     :=by
  sorry

-- -- this could be proven in a more general context of relations
lemma iso_eCodim_preserving {U : Set X} (U_open : IsOpen U)
    (f:RelIso (α := IrreducibleCloseds U)
      (β := {s : IrreducibleCloseds X // (U ∩ s).Nonempty})
      (· < ·) (· < ·) ) (a b : IrreducibleCloseds U): eCodim a b = eCodim (f a) (f b):= by
  -- use iso_length_preserving with both the RelIso way
  sorry



lemma codim_eq_sup_nonempty {U: Set X} (Y: IrreducibleCloseds X) (hU: (U ∩ Y).Nonempty):
  codim Y = ⨆ (s: {s:IrreducibleCloseds X // (U ∩ s).Nonempty}), eCodim Y s := by
  sorry


lemma length_equiv_inv {r: Rel (Set X) (Set X)}{a b : Set X} {s : Rel (Set X) (Set X)} (e: r ≃r s) (x : a -[r]→* b):
  x.reduce.length = (equiv e x).reduce.length := by
  cases x
  case singleton =>
    simp
    rfl

  case cons _ l hab  rr  =>
    simp [reduce]
    sorry



lemma eCodim_equiv_inv {r: Rel (Set X) (Set X)} {a b : Set X} {s : Rel (Set X) (Set X)} (e: r ≃r s) :
    eCodim a b = eCodim (e a) (e b):= by
  unfold eCodim
  unfold Rel.eCodim
  sorry



-- this is the theorem 5.11.2 to prove
theorem codimension_theorem [TopologicalSpace X]
    {U : Set X} (Y : IrreducibleCloseds X) (hU : IsOpen U) (hi : (U ∩ Y).Nonempty) :
    codim Y = codim (X:=U) (irr_closed_restrict Y hU hi):= by
  rw [codim_eq_sup_nonempty Y hi]

  dsimp [codim]

  apply Equiv.iSup_congr (closure_irred hU).toEquiv.symm
  simp
  intro a ha
  rw [iso_eCodim_preserving hU (closure_irred hU)
        (irr_closed_restrict Y hU hi)]

  sorry
