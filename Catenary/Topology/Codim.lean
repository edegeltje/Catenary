import Catenary.RelSeriesHT.Defs
import Mathlib.Topology.Sober
import Catenary.Order.Defs


open TopologicalSpace Set.Notation RelSeriesHT
variable {X : Type*} [TopologicalSpace X] {U : Set X}

lemma closure_irred_of_irred {U : Set X} (U_nonempty : U.Nonempty) (T : Set U) (T_irred : IsIrreducible T) : IsIrreducible (closure (X := X) T) := sorry

def closure_irred {U : Set X} (U_nonempty : U.Nonempty) (U_open : IsOpen U) : IrreducibleCloseds U → {s : IrreducibleCloseds X // ((s : Set X) ∩ U).Nonempty} := fun T ↦ ⟨⟨closure (X := X) T.carrier, closure_irred_of_irred U_nonempty T.carrier T.is_irreducible', isClosed_closure⟩, sorry⟩

def inter_irred (hU : IsOpen U) : {s : (IrreducibleCloseds X) // (U ↓∩ s).Nonempty } → IrreducibleCloseds U :=
  fun x =>
    ⟨U ↓∩ x,by
      have := x.val.isIrreducible.isPreirreducible
      constructor
      · exact x.prop

      rw [isPreirreducible_iff_isClosed_union_isClosed] at this ⊢
      intro z₁ z₂ hz₁ hz₂ hunion
      specialize this (closure z₁) (closure z₂) (isClosed_closure) isClosed_closure
      rw [← closure_union, ← Set.image_union] at this
      -- specialize this (exact?%)


      sorry
      ,x.val.isClosed.preimage_val⟩

lemma inter_irred_strictMono (hU : IsOpen U) : StrictMono (inter_irred hU) := by sorry

lemma closure_irred_bij {U : Set X} (U_open : IsOpen U) (U_nonempty : U.Nonempty) : Function.Bijective (closure_irred U_nonempty U_open):= sorry

example (hU : IsOpen U) (a b : IrreducibleCloseds X) : (a -[(· < ·)]→* b) → (inter_irred hU ⟨a,sorry⟩) -[(· < ·)]→* (inter_irred hU ⟨b,sorry⟩) := by
  sorry
  -- refine mapOrd _ (foo_strictMono hU)
