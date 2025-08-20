import Mathlib.Topology.Sober
import Mathlib.Topology.Order.Category.FrameAdjunction
import Mathlib.Topology.Category.Locale
import Mathlib.Topology.Homeomorph
import Mathlib.Topology.Specialization
import Mathlib.Topology.Order.ScottTopology
import Mathlib.Order.Basic
import Lean.Parser.Tactic
import Mathlib.Topology.Sets.Opens

import Semantics.Defs
import Semantics.TopologicalBasis

set_option autoImplicit false
open Locale TopCat CategoryTheory TopologicalSpace

def Sober (X : TopCat): Prop := QuasiSober X ∧ T0Space X

-- could use a TFAE block!
/-- Alternative definitions of Sober. Equivalence assumed -/
def adjunctionHomeomorphism {X: TopCat} : IsHomeomorph (adjunctionTopToLocalePT.unit.app X)
    ↔ Sober X := by sorry

variable {D : Type*} [AlgebraicDCPO D]

/-- Scott Topology on AlgebraicDCPO D -/
instance : TopologicalSpace D := Topology.scott D {d | DirectedOn (· ≤ ·) d}

/-- We claim that x is entirely determined by its set of basic opens `K x`.
    Proving this correspondence establishes the homeomorphism below. -/
abbrev K (x: PT (Opens D)) := { c | ∃ hc: c ∈ 𝕂 D, x <| open_of_compact c hc }

/-- Could add this to Mathlib. Lean's automation can prove this easily enough if a simp [map_sSup, sSup_Prop_eq].
    But I think using this lemma improves readability -/
lemma of_completelyPrime  {P: Opens D → Prop} {x: PT (Opens D)} : (x (sSup {u | P u})) ↔ ∃ u, P u ∧ x u := by
  simp only [map_sSup, sSup_Prop_eq]
  constructor
  · rintro ⟨h, ⟨h2, h3, h4⟩, h5⟩
    use h2
    subst h4
    exact ⟨h3, h5⟩
  · rintro ⟨u, hu, hxu⟩
    use x u
    simp only [Set.mem_image, Set.mem_setOf_eq, eq_iff_iff]
    constructor
    · use u
    · exact hxu

--lemma of_completelyPrime {x: PT (Opens D)} {P: Opens D → Prop} : (x (sSup {u | P u})) ↔ ∃ u, P u ∧ x u := by
--
--  u = sSup ({ o | ∃ (c: α) (hc: c ∈ 𝕂 α), (o = (open_of_compact c hc)) ∧ cᵘ ⊆ u}) := by

lemma directed_Kₓ (x: PT (Opens D)) : DirectedOn (· ≤ ·) (K x) := by
  rintro c ⟨hc₀, hc₁⟩ d ⟨hd₀, hd₁⟩
  let inf := (open_of_compact c hc₀) ⊓ (open_of_compact d hd₀)
  have inf_in_x : x inf := by
    simp only [map_inf, inf]
    exact ⟨hc₁, hd₁⟩

  have this := by
    rw [open_eq_open_of_basis' inf] at inf_in_x
    exact of_completelyPrime.1 inf_in_x
  obtain ⟨e', ⟨e, he₀, he'₀, he'₁⟩, he'₂⟩ := this

  rw [he'₁] at he'₂
  use e
  constructor
  · simp only [Set.mem_setOf_eq, inf]
    exact ⟨he₀, he'₂⟩
  · simp only [inf]
    simp [inf, open_of_compact] at he'₀
    obtain ⟨h₁, h₂⟩ := he'₀
    exact ⟨h₁, h₂⟩

-- TODO maybe this lemma is already in mathlib if i use `Ici`, Mathlib's version of upperSet
lemma le_iff_ge_upperSet {α: Type*} (c e : α) [Preorder α] : c ≤ e ↔ eᵘ ⊆ cᵘ := by
  simp [upperSet]
  constructor
  · intro hec x hxc
    exact Preorder.le_trans c e x hec hxc
  · intro x
    apply x e
    rfl

theorem scottIsSober : Sober (@TopCat.of D (Topology.scott D {d | DirectedOn (· ≤ ·) d})) := by
  apply adjunctionHomeomorphism.1
  -- #check (adjunctionTopToLocalePT.unit.app X)
  -- have : X ≃ₜ ((topToLocale ⋙ pt).obj X) := sorry
  constructor
  · -- continuity obtained since we have a morphism in the category of topological spaces
    -- should have been quite easy to prove...
    sorry
  · -- Open Map
    sorry
  · -- Bijective
    constructor
    · -- Injective
      -- change Function.Injective (λ _ → _)--(λ (d: X) → {U | IsOpen U ∧ d ∈ U}))
      -- #check ⇑(ConcreteCategory.hom (adjunctionTopToLocalePT.unit.app (TopCat.of D)))
      -- change Function.Injective ⇑(ConcreteCategory.hom (adjunctionTopToLocalePT.unit.app (TopCat.of D)))
      -- have t0 : T0Space Y := sorry

      intro d e
      contrapose
      intro d_ne_e
      dsimp only [Functor.id_obj] at d e
      simp only [Functor.comp_obj, topToLocale_obj, Functor.id_obj]

      -- have foo (d_nle_e: _) := True
      -- these simplifications should be deduplicated across the cases
      dsimp only [Functor.id_obj, Functor.comp_obj, topToLocale_obj, adjunctionTopToLocalePT,
        topCatOpToFrm_obj_coe, hom_ofHom]
      change ¬ ((localePointOfSpacePoint D d) = (localePointOfSpacePoint D e))
      rw [@FrameHom.ext_iff (Opens D) Prop (Opens.instCompleteLattice) Prop.instCompleteLattice (localePointOfSpacePoint D d) (localePointOfSpacePoint D e)]
      simp only [localePointOfSpacePoint_toFun, eq_iff_iff, not_forall]
      rcases (@Ne.not_le_or_not_le D _ _ _ d_ne_e) with d_nle_e | e_nle_d
      ·
        simp only [specialization_iff_ge, specializes_iff_forall_open, not_forall,
          Classical.not_imp] at d_nle_e
        obtain ⟨u, hu, d_in_u, e_in_u⟩ := d_nle_e
        use ⟨u, hu⟩
        simp only [Opens.mem_mk]
        intro h
        exact (and_not_self_iff (e ∈ u)).1 ⟨h.1 d_in_u, e_in_u⟩
      · sorry
    · -- Surjective
      intro x
      simp only [Functor.comp_obj] at x
      dsimp [pt, PT] at x
      let Kₓ := K x
      let inp := sSup Kₓ
      use inp
      dsimp only [Functor.id_obj, Functor.comp_obj, topToLocale_obj, adjunctionTopToLocalePT,
        topCatOpToFrm_obj_coe, hom_ofHom]
      apply FrameHom.ext
      intro u
      dsimp only [topCatOpToFrm_obj_coe] at u
      simp only [eq_iff_iff]
      change sSup Kₓ ∈ u ↔ x u

      calc
        _ ↔ sSup Kₓ ∈ u.carrier := by rfl
        _ ↔ sSup Kₓ ∈ ⋃₀ (upperSet '' { e ∈ 𝕂 D | eᵘ ⊆ u}) := by
          nth_rewrite 1 [open_eq_open_of_basis u.carrier u.isOpen]
          rfl
        _ ↔ ∃ e ∈ 𝕂 D, eᵘ ⊆ u ∧ e ≤ sSup Kₓ := by
          constructor
          · rintro ⟨e', he'₀, he'₁⟩
            simp only [Set.mem_image, Set.mem_setOf_eq] at he'₀
            choose e he₁ he₂ using he'₀
            use e
            simp only [← he₂, upperSet, Set.mem_setOf_eq] at he'₁
            exact ⟨he₁.1, he₁.2, he'₁⟩
          · rintro ⟨e, he₀, he₁, he₂⟩
            have he'₀ : eᵘ ∈ (upperSet '' {c | c ∈ 𝕂 D ∧ cᵘ ⊆ u}) := by
              simp only [Set.mem_image, Set.mem_setOf_eq]
              use e
            apply Set.subset_sUnion_of_mem at he'₀
            have he₂ : sSup Kₓ ∈ eᵘ := by aesop
            exact Set.mem_of_mem_of_subset he₂ he'₀
        _ ↔ ∃ (e c : D), c ∈ Kₓ ∧ e ∈ 𝕂 D  ∧ eᵘ ⊆ u ∧ e ≤ c := by
            constructor
            · rintro ⟨e, he₀, he'₀, he₁⟩
              use e
              choose c hc₁ hc₂ using he₀ Kₓ (directed_Kₓ x) he₁
              use c
            · rintro ⟨e, c, hc₀, he₀, he'₀, e_le_c⟩
              use e
              have he₁ : e ≤ sSup Kₓ := by
                trans c
                · assumption
                · have sSup_is_LUB := CompletePartialOrder.lubOfDirected Kₓ (directed_Kₓ x)
                  exact sSup_is_LUB.1 hc₀
              exact ⟨he₀, he'₀, he₁⟩
        _ ↔ ∃ (e c : D) (hc: c ∈ 𝕂 D), e ∈ 𝕂 D ∧ eᵘ ⊆ u ∧ cᵘ ⊆ eᵘ ∧ x (open_of_compact c hc) := by
          constructor
          · rintro ⟨e, c, ⟨hc₀, hc₁⟩, he₀, he₁, e_le_c⟩
            use e; use c; use hc₀
            exact ⟨he₀, he₁, by rwa [← le_iff_ge_upperSet e c], hc₁⟩

          · rintro ⟨e, c, hc₀, he₀, he'₀, c'_le_e', hc'₀⟩
            use e; use c;
            exact ⟨⟨hc₀, hc'₀⟩, he₀, he'₀, by rwa [le_iff_ge_upperSet e c]⟩
        _ ↔ ∃ (e: D) (he: e ∈ 𝕂 D), eᵘ ⊆ u ∧ x (open_of_compact e he) := by
          constructor
          · rintro ⟨e, c, hc₀, he₀, he'₀, c'_le_e', hc'₀⟩
            use e; use he₀; use he'₀
            let cU := (open_of_compact c hc₀)
            let eU := (open_of_compact e he₀)
            have foo : cU ⊓ eU = cU := by simpa [open_of_compact, cU, eU]
            have bar : x (cU ⊓ eU) = x cU := by simp_all
            simp [map_sSup] at bar
            exact bar hc'₀
          · -- the reverse direction is a bit silly as the requirements for c are all satisfied by e itself
            intro ⟨e, he₀, he'₀, he'₁⟩
            use e; use e; use he₀;
        _ ↔ x u := by
          constructor
          · let P (o: Opens D) := ∃ (c: D) (hc: c ∈ 𝕂 D), c ∈ u ∧ (o = (open_of_compact c hc))
            -- intro he
            rintro ⟨e, he₀, he'₀, he'₁⟩
            have he': ∃ u, P u ∧ x u := by
              use (open_of_compact e he₀)
              exact ⟨⟨e, he₀, mem_iff_upSet_subset.2 he'₀, rfl⟩, he'₁⟩

            rw [← of_completelyPrime] at he'
            rw [← open_eq_open_of_basis' u] at he'
            exact he'
          · intro hu
            rw [open_eq_open_of_basis' u] at hu
            rw [of_completelyPrime] at hu

            obtain ⟨e', ⟨e, he₀, he'₀, he'₁⟩ , he'₂⟩ := hu
            rw [he'₁] at he'₂
            exact ⟨e, he₀, mem_iff_upSet_subset.1 he'₀, he'₂⟩
