import Mathlib.Data.ENat.Lattice
import Mathlib.Topology.Basic
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Sets.Closeds
import Mathlib.Topology.Sets.OpenCover
import Mathlib.Topology.Constructions
import Mathlib.Topology.IsLocalHomeomorph
import Catenary.RelSeriesHT.Defs
import Catenary.RelSeriesHT.Codim
import Catenary.Order.Defs
import Catenary.Topology.Codim

open TopologicalSpace Rel RelSeriesHT ENat Set Topology Homeomorph Set.Notation

namespace TopologicalSpace

variable (X : Type) [TopologicalSpace X]

abbrev IsCatenaryTopologicalSpace := IsCatenaryOrder (IrreducibleCloseds X)
abbrev IsIrreduciblyNoetherianTopologicalSpace := IsDiscreteOrder (IrreducibleCloseds X)

noncomputable def top_open_homeo_univ : (⊤ : Opens X) ≃ₜ X := IsEmbedding.toHomeomorph_of_surjective Topology.IsEmbedding.subtypeVal (by intro x; use ⟨x, trivial⟩)

lemma isCatenary_of_iso_isCatenary {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (Y_catenary : IsCatenaryTopologicalSpace Y) (φ : X ≃ₜ Y) : IsCatenaryTopologicalSpace X := ⟨by
  intro T T'
  obtain ⟨n, h⟩ := Y_catenary.isCatenary ⟨(φ '' T), sorry, sorry⟩ ⟨(φ '' T'), sorry, sorry⟩
  use n
  intro x
  sorry⟩

-- lemma 5.11.5 part 1
lemma catenary_iff_catenary_cover : IsCatenaryTopologicalSpace X ↔ ∃ ι : Type, ∃ u : ι → Opens X, IsOpenCover u ∧ ∀ i : ι, IsCatenaryTopologicalSpace (u i) := by
  constructor
  · intro h
    use Finset.range 1, fun i ↦ ⊤
    constructor
    · simp only [IsOpenCover, Finset.range_one, ciSup_unique]
    · simp only [Finset.range_one, Finset.mem_singleton, forall_const]
      exact isCatenary_of_iso_isCatenary h (top_open_homeo_univ X)
  · intro exists_cat_cov
    constructor
    intro T T'
    by_cases h : T = T'
    · simp
      use 0
      intro x
      use x, (by rfl)
      subst h
      match x with
      | RelSeriesHT.singleton T => rfl
      | RelSeriesHT.cons (b := b) T2 l Tltb =>
        have : T2 ≠ b := by
          intro hT2b
          subst hT2b
          exact lt_irrefl T2 Tltb
        have := le_of_lt (lt_of_relSeriesHT this.symm l)
        have := Tltb.right
        contradiction
    · push_neg at h
      by_cases TltT' : ¬ T < T'
      · use 0
        intro x
        have : T < T' := lt_of_relSeriesHT h x
        contradiction
      push_neg at TltT'
      obtain ⟨ι, u, u_cov, ui_cat⟩ := exists_cat_cov
      have : ∃ i, ((u i : Set X) ∩ T).Nonempty := by
        obtain ⟨t, t_mem_T⟩ := T.is_irreducible'.1
        obtain ⟨i, t_mem_ui⟩ := IsOpenCover.exists_mem u_cov t
        use i, t
        constructor <;> assumption
      obtain ⟨i, ui_inter⟩ := this
      have ui_inter' : ((u i : Set X) ∩ T').Nonempty := by
        obtain ⟨x, x_mem⟩ := ui_inter
        use x, x_mem.left
        apply mem_of_mem_of_subset x_mem.right
        simp only [SetLike.coe_subset_coe]
        exact le_of_lt TltT'
      obtain ⟨n, h⟩ := (ui_cat i).isCatenary ((closure_irred (u i).is_open').invFun ⟨T, ui_inter⟩) ((closure_irred (u i).is_open').invFun ⟨T', ui_inter'⟩) -- can use properties of closure_irred for this?
      use n
      intro x
      let xui := (order_iso (closure_irred (u i).is_open').symm (copy_inter ui_inter ui_inter' x))
      simp [closure_irred, irr_closed_restrict] at xui
      obtain ⟨yui, hui⟩ := h xui
      simp [closure_irred, irr_closed_restrict] at yui
      let y' := order_iso (closure_irred (u i).is_open') yui
      simp [closure_irred] at y'
      let y := @coe_subtype (IrreducibleCloseds X) (r := (· < ·)) (p := fun T ↦ ((u i : Set X) ∩ T).Nonempty) _ _ y'
      have closure_irred_T : closure (X := X) ((u i : Set X) ↓∩ T) = T := sorry
      have closure_irred_T' : closure (X := X) ((u i : Set X) ↓∩ T') = T' := sorry
      simp [closure_irred_T, closure_irred_T'] at y
      use y
      use isReduced_of_irrefl y
      constructor
      · sorry
      · sorry
      -- rw [← closure_irred_T] at x
      -- have := (order_iso (closure_irred (u i).is_open')).map_rel_iff'.mpr
      -- apply (order_iso (closure_irred (u i).is_open')).map_rel_iff'.mpr

-- lemma 5.11.5 part 2
lemma locally_closed_subspace_catenary_of_catenary : IsCatenaryTopologicalSpace X → ∀ Y : Set X, IsLocallyClosed Y → IsCatenaryTopologicalSpace Y := sorry

/--
A topological space is irreducibly Noetherian if and only if the irreducibles satisfy the descending chain condition.
-/
lemma irreducibly_noetherian_iff_codim_lt_infty : IsIrreduciblyNoetherianTopologicalSpace X ↔ ∀ Y Y' : IrreducibleCloseds X, eCodim Y Y' < ⊤ := RelSeriesHT.isDiscrete_iff_forall_eCodim_lt_top

/--
A topological space is catenary if and only if it is irreducibly Noetherian and satisfies the dimension formula.
-/
@[stacks 02I6]
lemma catenary_iff_dimension_formula : IsCatenaryTopologicalSpace X ↔ IsIrreduciblyNoetherianTopologicalSpace X ∧ ∀ Y Y' Y'' : IrreducibleCloseds X, Y < Y' → Y' < Y'' → eCodim Y Y' + eCodim Y' Y'' = eCodim Y Y'' := isCatenaryOrder_iff_isDiscreteOrder_and_dimension_formula (IrreducibleCloseds X)

end TopologicalSpace
