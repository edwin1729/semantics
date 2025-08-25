import Mathlib.Topology.Sets.Opens

import Semantics.Defs

set_option autoImplicit false

open Topology.IsScott TopologicalSpace Set Topology

variable {α : Type*} [CompletePartialOrder α]

instance : TopologicalSpace α := Topology.scott α {d | DirectedOn (· ≤ ·) d}
-- We create the IsScott instance in order to use some Mathlib
-- particularly `isOpen_iff_isUpperSet_and_dirSupInaccOn`
instance : IsScott α {d | DirectedOn (· ≤ ·) d} := ⟨by rfl⟩

-- This goal is very obvious but `simp_all` makes no progress `apply?` doesn't seem to be helpful
-- aesop gives the below which is too big, for something so simple.
-- aesop doesn't work at the call site as it exceeds maxRecDepth (and manually increasing this causes stackoverflow)
-- Soooo, I awkwardly pull this lemma out and use aesop.
lemma aesopify {α : Type*} {compact: α -> Prop } {x: α} [LE α] {u: Set α} (a: ∃ c, (c ≤ x ∧ compact c) ∧ c ∈ u) : ∃ c ≤ x, c ∈ u ∧ compact c := by
  aesop

lemma h_open {u: Set α} (hu: u ∈ upperSet '' 𝕂 α): IsOpen u := by
    rw [@isOpen_iff_isUpperSet_and_dirSupInaccOn α {d | DirectedOn (· ≤ ·) d }]
    constructor
    · -- u is an upper set
      unfold IsUpperSet
      intro a b a_1 a_2
      simp_all only [mem_image]
      obtain ⟨w, h⟩ := hu
      obtain ⟨left, right⟩ := h
      subst right
      -- unfold _root_.upperSet at a_2 ⊢
      simp only [_root_.upperSet, mem_setOf_eq] at a_2 ⊢
      transitivity a
      · exact a_2
      · exact a_1
    · -- u is a Scott-Hausdorff open set, ie it has the inaccessable directed joins property
      -- However the directed sets for our topology are defined precisely as the directed sets of the our DCPOs
      -- So compact elements are precisely those elements which have directed innaccessable joins
      intro d hd nonempty _  x hx hx'
      simp at hu
      choose y yCompact yUpper using hu
      -- rewrite `x`'s LUB propoerty in terms of sSup
      have hx : x = sSup d := by
        have hsSupd := CompletePartialOrder.lubOfDirected d hd
        exact IsLUB.unique hx hsSupd

      have hy : y ≤ sSup d := by
        rw [← hx]

        subst yUpper
        simp only [_root_.upperSet, mem_setOf_eq] at hx'
        exact hx'

      choose a a_in_d ha' using yCompact d hd hy
      have a_in_u : a ∈ u := by aesop
      use a
      constructor
      · exact a_in_d
      · exact a_in_u

-- notation for this would be nice especially for the cᵘ ∩ dᵘ thing
def open_of_compact (c : {c: α // compact c}) : Opens α :=
  ⟨cᵘ, h_open <| Set.mem_image_of_mem upperSet c.2⟩
notation c:80"ᵘᵒ"  => open_of_compact c -- upperSet, open


lemma mem_iff_upSet_subset {e: α} {u: Opens α}: e ∈ u ↔ eᵘ ⊆ u := by
  constructor
  · intro e_in_u
    have u_open := u.isOpen
    rw [@isOpen_iff_isUpperSet_and_dirSupInaccOn α {d | DirectedOn (· ≤ ·) d }] at u_open
    let ⟨u_upperSet, _⟩ := u_open
    intro a ha
    exact u_upperSet ha e_in_u
  · rintro h
    exact Set.mem_of_mem_of_subset (by simp only [_root_.upperSet, mem_setOf_eq, le_refl]) h

-- Should be moved to scott_topology.lean
/-- Unfortunately under Mathlib's for specialization is opposite our existing order -/
lemma specialization_iff_ge {x y : α}: x ≤ y ↔ y ⤳ x := by
  rw [specializes_iff_forall_open]
  constructor
  · intro x_le_y u hu x_in_u
    apply (@isUpperSet_of_isOpen α {d | DirectedOn (· ≤ ·) d }) at hu
    exact hu x_le_y x_in_u
  ·
    let u := {z : α | ¬(z ≤ y)}
    have hu: IsOpen u := by
      rw [@isOpen_iff_isUpperSet_and_dirSupInaccOn α {d | DirectedOn (· ≤ ·) d }]
      constructor
      · intro a b a_le_b a_in_u b_le_y
        exact (and_not_self_iff (a ≤ y)).1 ⟨a_le_b.trans b_le_y, a_in_u⟩
      · intro d hd hd₁ _ join h_join join_in_u
        by_contra inter_empty
        simp only [Set.Nonempty, mem_inter_iff, mem_setOf_eq, not_exists, not_and, not_not,
          u] at inter_empty
        have join_le_y : join ≤ y := by
          have y_in_UB_d : y ∈ upperBounds d := by
            simp_all only [mem_setOf_eq, u]
            exact inter_empty
          have h_join := isLUB_iff_le_iff.1 h_join y
          rwa [←  h_join] at y_in_UB_d
        exact (and_not_self_iff (join ≤ y)).1 ⟨join_le_y, join_in_u⟩

    intro h_specialize
    -- Take the contrapose of x being in an open implying y must also be in it
    have h_specialize := not_imp_not.2 <| h_specialize u hu
    -- we know y ∉ u as y ≤ y. And from specialization relation on y we deduce that x ∉ u
    simp only [mem_setOf_eq, le_refl, not_true_eq_false, not_false_eq_true, not_not, forall_const,
      u] at h_specialize
    -- in other words x ≤ y as required
    exact h_specialize

variable {D : Type*} [AlgebraicDCPO D]

lemma h_nhds (x : D) (u : Set D) (x_in_u : x ∈ u) (hu : IsOpen u)
  : ∃ v ∈ _root_.upperSet '' 𝕂 D, x ∈ v ∧ v ⊆ u := by

    rw [@isOpen_iff_isUpperSet_and_dirSupInaccOn D {d | DirectedOn (· ≤ ·) d }] at hu

    obtain ⟨upper, hausdorff⟩ := hu
    have compactLowerBounded : ∀ x ∈ u, ∃ c: D, c ≤ x ∧ c ∈ u ∧ compact c := by
      intro x x_in_u
      -- the Algebraicity property
      obtain ⟨nonempty, directedCls, join⟩ := AlgebraicDCPO.algebraic x
      -- simp only [Function.comp_apply] at hausdorff

      -- We work with this cls to extract a compact elememt from it satisfying our needs
      let cls := (compactLowerSet x)

      -- by algebraicity, an element, `x`, is the meet of its `cls`
      have x_is_LUB : IsLUB cls x:= by
        rw [join]
        apply CompletePartialOrder.lubOfDirected cls directedCls

      -- We use the innacessible joins property to show get a nonempty intersection
      -- The intersection contains exactly what we want, a compact element in u and ≤ x
      have nonempty_inter := hausdorff directedCls nonempty directedCls x_is_LUB x_in_u
      simp only [compactLowerSet, inter_nonempty, mem_inter_iff, mem_setOf_eq] at nonempty_inter

      -- This is the funny bit where I decided it's cleanest to extract boilerplate to `aesopify`
      -- didn't figure out where or how I was running into infinite recursion on direct `aesop`
      change ∃ c, (c ≤ x ∧ compact c) ∧ c ∈ u at nonempty_inter
      have : ∃ c ≤ x, c ∈ u ∧ compact c:= aesopify nonempty_inter
      exact this

    -- given an x ∈ u, take it to its compact element
    choose f hf hf' hf'' using compactLowerBounded
    let f' : {x : D // x ∈ u} → D := λ x => f x.1 x.2
    let upSetC := _root_.upperSet (f' ⟨x, x_in_u⟩)
    use upSetC

    constructor
    · simp only [_root_.upperSet, mem_image]
      use (f' ⟨x, x_in_u⟩)
      constructor
      · apply hf''
      · aesop
    · constructor
      · apply hf
      · intro y hy
        aesop

-- below is comment is copied from reference
/-- Proposition 3.5.2. Let (D, ⊑) be an algebraic DCPO. Then the set of opens
   ↑ KD = { ↑ c | c ∈ KD}
   is a subbasis for ΣD

   Proof. Let U be a Scott-open set. Then we have that U = S{ ↑ c | c ∈
   U ∩ KD}, since for any x ∈ U, by the algebraicity of D, there is a
   compact element c ⊑ x in U, so x ∈ ↑ c ⊆ U -/
lemma scott_is_upset : IsTopologicalBasis (upperSet '' 𝕂 D) := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · -- every upper set of a compact element in the DCPO is a Scott open set
    -- This is the true by definition direction, as compactness corresponds to Scott-Hausdorrf open,
    -- and upper set corresponds to Upper set open
    apply h_open
  · -- If an element `x` is in an open set `u`, we can find it in a set in the basis (`upperSet c`)
    apply h_nhds

/-- Any open set, `u`, can be constructed as a union of sets from the basis.
    The basis consists of the upward closures of those compact elements in `u`
    This is the weaker version of the lemma using `Set`s instead of `Opens`-/
lemma open_eq_open_of_basis (u : Set D) (hu: IsOpen u) :
  u = ⋃₀ (upperSet '' { c ∈ 𝕂 D | cᵘ ⊆ u}) := by
  ext x
  simp only [SetLike.mem_coe, sUnion_image, mem_setOf_eq, mem_iUnion, exists_prop]
  constructor
  · intro x_in_u
    have foo := h_nhds x u x_in_u hu
    choose a b c d using foo
    obtain ⟨e, f⟩ := b
    use e
    simp_all only [Opens.carrier_eq_coe, and_self]
  ·
    rintro ⟨y, ⟨c, hc⟩, h⟩
    apply hc
    simp_all only

/-- See `open_eq_open_of_basis`
    This is the stronger version of the lemma using `Opens` instead of `Set`s.
    I don't reuse the previous result to prove this, since the proof turns out just as long-/
lemma open_eq_open_of_basis' (u : Opens D) :
  u = sSup ({ o | ∃ (c: D) (hc: c ∈ 𝕂 D), c ∈ u ∧ (o = ⟨c,hc⟩ᵘᵒ) }) := by
  ext e
  simp only [SetLike.mem_coe, sSup_image, mem_setOf_eq, mem_iUnion, exists_prop]
  constructor
  · intro e_in_u
    choose c' hc'₀ e_in_c' hc'₁ using h_nhds e u e_in_u u.isOpen
    simp only [Opens.mem_sSup]
    use ⟨c', h_open hc'₀⟩
    constructor
    ·
      obtain ⟨c, hc₀, c'_eq⟩ := hc'₀
      simp only [open_of_compact]
      rw [← c'_eq] at hc'₁
      use c ;use hc₀; use mem_iff_upSet_subset.2 hc'₁
      simp only [Opens.mk.injEq]
      exact id (Eq.symm c'_eq)
    · exact e_in_c'
  ·
    rintro he
    simp only [Opens.mem_sSup] at he
    obtain ⟨c', hc'₀, he⟩ := he
    obtain ⟨c, hc₀, hc₁, hc'₁⟩ := hc'₀
    rw [mem_iff_upSet_subset] at hc₁
    rw [open_of_compact] at hc'₁
    rw [hc'₁] at he
    exact Set.mem_of_mem_of_subset he hc₁
