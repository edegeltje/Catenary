import Catenary.RelSeriesHT.Defs
import Mathlib.Topology.Sober
import Catenary.Order.Defs


open TopologicalSpace Set.Notation RelSeriesHT
variable {X : Type*} [TopologicalSpace X] {U : Set X}


def foo (hU : IsOpen U) : {s : (IrreducibleCloseds X) // (U ↓∩ s).Nonempty } → IrreducibleCloseds U :=
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

lemma foo_strictMono (hU : IsOpen U) : StrictMono (foo hU) := by sorry


example (hU : IsOpen U) (a b : IrreducibleCloseds X) : (a -[(· < ·)]→* b) → (foo hU ⟨a,sorry⟩) -[(· < ·)]→* (foo hU ⟨b,sorry⟩) := by
  sorry
  -- refine mapOrd _ (foo_strictMono hU)
