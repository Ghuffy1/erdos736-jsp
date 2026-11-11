import Erdos736

open SimpleGraph Cardinal

universe u

namespace StatementCheck

/-- The original assertion with ordinary finite copies written out explicitly. -/
def OriginalAssertion : Prop :=
  ∀ (V : Type u) (G : SimpleGraph V), Erdos736.chromaticCardinal G = ℵ₁ →
    ∀ m : Cardinal.{u}, ∃ (W : Type u) (H : SimpleGraph W), Erdos736.chromaticCardinal H = m ∧
      ∀ (U : Type u) [Fintype U] (F : SimpleGraph U),
        (∃ e : U → W, Function.Injective e ∧ ∀ a b, F.Adj a b → H.Adj (e a) (e b)) →
        ∃ e : U → V, Function.Injective e ∧ ∀ a b, F.Adj a b → G.Adj (e a) (e b)

theorem original_assertion_false : ¬OriginalAssertion.{u} := Erdos736.erdos_736

#print axioms original_assertion_false
#check original_assertion_false

end StatementCheck
