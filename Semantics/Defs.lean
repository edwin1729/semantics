import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Order.ScottTopology
import Mathlib.Topology.Bases
import Mathlib.Topology.Order

set_option autoImplicit false
-- unfortunately a different notion of compact
-- import Mathlib.Topology.Compactness.Compact

-- compactness (in the sense we want) is sadly only defined for CompleteLattice in the below file
-- import Mathlib.Order.CompactlyGenerated.Basic

-- Notation from [Abramsky and Jung, *Domain Theory*][abramsky_gabbay_maibaum_1994]
-- These definitons are also in the report

/-- notation for downward closure -/
notation "↓" x:80 => Set.Iic x
/-- notation for upward closure (↑ was taken) -/
notation x:80 "ᵘ" => Set.Ici x

/-- approximants: read as x is way smaller than y-/
def approx  {α : Type*} [CompletePartialOrder α] (x: α) (y: α) := ∀ (d : Set α), DirectedOn (· ≤ ·) d → y ≤ sSup d → ∃ a ∈ d, x ≤ a
/-- notation for approx (approximants in `CompletePartialOrder`)-/
notation x:80 "⟪" y:80 => approx x y

/-- x approximates itself: key property and abstracted by the
`DirSupInacc` (inacessibility of directed joins property) -/
def compact {α : Type*} [CompletePartialOrder α](x: α) := approx x x
/-- Set of compact elements-/
def compactSet (α : Type*) [CompletePartialOrder α] := {x : α | compact x}
/-- notation for compactSet -/
notation "𝕂" α:80 => compactSet α

/-- Intersection-/
def compactLowerSet {α : Type*} [CompletePartialOrder α] (x: α) := ↓x ∩ 𝕂 α

/-- Encodes notion of observable properties in programs (elements)-/
class AlgebraicDCPO (α : Type*) extends CompletePartialOrder α where
  algebraic : ∀ x : α, (compactLowerSet x).Nonempty ∧ DirectedOn (· ≤ ·) (compactLowerSet x) ∧ x = sSup (compactLowerSet x)

-- consider using namespace for algebraic dcpo
noncomputable def lowerCompact_of_point {α : Type*} [AlgebraicDCPO α] (x: α) : {c : α // c ≤ x ∧ c ∈ 𝕂 α} := by
  let ⟨a,b,d⟩ := AlgebraicDCPO.algebraic x
  choose a₁ a₂ a₃ using a
  exact ⟨a₁, a₂, a₃⟩
