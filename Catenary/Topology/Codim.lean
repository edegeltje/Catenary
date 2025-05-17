import Catenary.RelSeriesHT.Defs
import Mathlib.Logic.Function.Defs
import Catenary.RelSeriesHT.Codim
import Mathlib.Topology.Sober
import Catenary.Order.Defs


open TopologicalSpace Set.Notation RelSeriesHT Function
variable {X : Type*} [TopologicalSpace X] {U : Set X}


-- General results

lemma closure_irred_of_irred {U : Set X} (T : Set U) (T_irred : IsIrreducible T) : IsIrreducible (closure (X := X) T) := by
 sorry

def closure_irred {U : Set X} (U_open : IsOpen U) : RelIso (α := IrreducibleCloseds U) (β := {s : IrreducibleCloseds X // (U ↓∩ s).Nonempty}) (· < ·) (· < ·) where
  toFun := fun T ↦ ⟨⟨closure (X := X) T.carrier, closure_irred_of_irred T.carrier T.is_irreducible', isClosed_closure⟩, sorry⟩
  invFun := fun x =>
    ⟨U ↓∩ x,by
      have := x.val.isIrreducible.isPreirreducible
      constructor
      · exact x.prop

      rw [isPreirreducible_iff_isClosed_union_isClosed] at this ⊢
      intro z₁ z₂ hz₁ hz₂ hunion
      specialize this (closure z₁) (closure z₂) (isClosed_closure) isClosed_closure
      -- rw [← closure_union, ← Set.image_union] at this
      -- specialize this (exact?%)
      sorry
      ,x.val.isClosed.preimage_val⟩
  left_inv := sorry
  right_inv := sorry
  map_rel_iff' := sorry

lemma closure_strict_mono_on_irreducible_closed {U : Set X} {A B: IrreducibleCloseds U}  (r: A < B) : (closure A.carrier) < (closure B) := by
  sorry

--
-- Sup and bijection


lemma l {A: Set X} {B: Set X} (T: A → B) (f: X → Nat) (hT: Bijective T) (hf: ∀ a : A, f a = f (T a) ):
  -- f '' A = f '' (Subtype.val '' (T '' (Set.univ : Set (Subtype A)))) :=
  f '' A = f '' (T '' A) := by
  sorry


lemma supremum_bijection_preserving {A: Set X} {B: Set X} (T: A → B) (f: X → Nat) (hT: Bijective T) (hf: ∀ a : A, f a = f (T a) ):
  ⨆ (a ∈ A), f a  = ⨆ (b ∈ B), f b := by
  sorry

noncomputable def closure_of_irreducible_subset {U: Set X} (A: IrreducibleCloseds U): IrreducibleCloseds X :=
  ⟨closure (A: Set U), sorry,  by exact isClosed_closure⟩


lemma foo_strictMono: StrictMono (closure_of_irreducible_subset : IrreducibleCloseds U → IrreducibleCloseds X) := by sorry
--
-- Codimensions

-- lemma closure_ecodim_preserving {Y: IrreducibleCloseds X} {U: Set X}{Z: IrreducibleCloseds X}(hU: IsOpen U)(hi: (U ∩ Y).Nonempty):
--   eCodim Y Z = eCodim ⟨closure (Y ∩ U), sorry, sorry⟩ Z := by
--   sorry

-- lemma closure_ecodim_preserving

noncomputable def codim [TopologicalSpace X] (Y: IrreducibleCloseds X) : WithBot ℕ∞ :=
    ⨆ (U: IrreducibleCloseds X), (eCodim Y U)

example (hU : IsOpen U) (a b : IrreducibleCloseds X) : (a -[(· < ·)]→* b) → ((closure_irred hU).invFun ⟨a,sorry⟩) -[(· < ·)]→* ((closure_irred hU).invFun ⟨b,sorry⟩) := by
  sorry

-- not sure if it's needed
lemma codim_nonneg [TopologicalSpace X] (Y: IrreducibleCloseds X) : 0 ≤ codim Y := by
  sorry

-- this is the theorem 5.11.2 to prove
theorem codimension_theorem [TopologicalSpace X]
    {U: Set X}(Y: IrreducibleCloseds X) (hU: IsOpen U)(hi: (U ∩ Y).Nonempty ) :
    -- codim Y = @codim U _ ⟨((U ↓∩ Y): Set U), sorry, sorry ⟩
    codim Y = 1
    := by
  dsimp [codim]

  sorry
