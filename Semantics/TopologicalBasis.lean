import Mathlib.Topology.Sets.Opens

import Semantics.Defs

set_option autoImplicit false

open Topology.IsScott TopologicalSpace Set Topology

instance (α : Type*) [CompletePartialOrder α] : TopologicalSpace α := Topology.scott α {d | DirectedOn (· ≤ ·) d}
-- We create the IsScott instance in order to use some Mathlib
-- particularly `isOpen_iff_isUpperSet_and_dirSupInaccOn`
instance (α : Type*) [CompletePartialOrder α] : IsScott α {d | DirectedOn (· ≤ ·) d} := ⟨by rfl⟩

-- This goal is very obvious but `simp_all` makes no progress `apply?` doesn't seem to be helpful
-- aesop gives the below which is too big, for something so simple.
-- aesop doesn't work at the call site as it exceeds maxRecDepth (and manually increasing this causes stackoverflow)
-- Soooo, I awkwardly pull this lemma out and use aesop.
lemma aesopify {α : Type*} {compact: α -> Prop } {x: α} [LE α] {u: Set α} (a: ∃ c, (c ≤ x ∧ compact c) ∧ c ∈ u) : ∃ c ≤ x, c ∈ u ∧ compact c := by
  aesop

variable {α : Type*} [AlgebraicDCPO α]

lemma h_nhds
(x : α)
(u : Set α)
(x_in_u : x ∈ u)
(hu : IsOpen u)
: ∃ v ∈ _root_.upperSet '' 𝕂 α, x ∈ v ∧ v ⊆ u := by

    rw [@isOpen_iff_isUpperSet_and_dirSupInaccOn α {d | DirectedOn (· ≤ ·) d }, DirSupInaccOn] at hu

    obtain ⟨upper, hausdorff⟩ := hu
    have compactLowerBounded : ∀ x ∈ u, ∃ c: α, c ≤ x ∧ c ∈ u ∧ compact c := by
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
    let f' : {x : α // x ∈ u} → α := λ x => f x.1 x.2
    let upSetC := _root_.upperSet (f' ⟨x, x_in_u⟩)
    use upSetC

    constructor
    ·
      simp only [_root_.upperSet, mem_image]
      use (f' ⟨x, x_in_u⟩)
      constructor
      · apply hf''
      · aesop
    · constructor
      · apply hf
      · intro y hy
        aesop

lemma h_open {u: Set α} (hu: u ∈ upperSet '' 𝕂 α): IsOpen u := by
    rw [@isOpen_iff_isUpperSet_and_dirSupInaccOn α {d | DirectedOn (· ≤ ·) d }, DirSupInaccOn]
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
-- below is comment is copied from reference
/-- Proposition 3.5.2. Let (D, ⊑) be an algebraic DCPO. Then the set of opens
   ↑ KD = { ↑ c | c ∈ KD}
   is a subbasis for ΣD

   Proof. Let U be a Scott-open set. Then we have that U = S{ ↑ c | c ∈
   U ∩ KD}, since for any x ∈ U, by the algebraicity of D, there is a
   compact element c ⊑ x in U, so x ∈ ↑ c ⊆ U -/
lemma scott_is_upset : IsTopologicalBasis (upperSet '' 𝕂 α) := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · -- every upper set of a compact element in the DCPO is a Scott open set
    -- This is the true by definition direction, as compactness corresponds to Scott-Hausdorrf open,
    -- and upper set corresponds to Upper set open
    apply h_open
  · -- If an element `x` is in an open set `u`, we can find it in a set in the basis (`upperSet c`)
    apply h_nhds

-- refactor
lemma constructOpenFromCompact (u : Opens α)  :
  u = ⋃₀ (upperSet '' { c ∈ 𝕂 α | cᵘ ⊆ u}) := by
    ext x
    simp only [SetLike.mem_coe, sUnion_image, mem_setOf_eq, mem_iUnion, exists_prop]
    constructor
    · intro x_in_u
      have foo := h_nhds x u.carrier x_in_u u.isOpen
      choose a b c d using foo
      obtain ⟨e, f⟩ := b
      use e
      simp_all only [Opens.carrier_eq_coe, and_self]
    ·
      rintro ⟨y, ⟨c, hc⟩, h⟩
      apply hc
      simp_all only
