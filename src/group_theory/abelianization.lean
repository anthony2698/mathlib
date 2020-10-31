/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Michael Howes

The functor Grp → Ab which is the left adjoint
of the forgetful functor Ab → Grp.
-/

import group_theory.quotient_group
import tactic.group

universes u v

/--

TODO: If `H K : subgroup G` then define `commutator H K : subgroup G`

--/

-- let G be a group
variables (G : Type u) [group G](H₁ : subgroup G)(H₂  : subgroup G)

/-- The commutator subgroup of a group G is the normal subgroup
  generated by the commutators [p,q]=`p*q*p⁻¹*q⁻¹` -/
@[derive subgroup.normal]
def commutator  (H₁ : subgroup G)(H₂  : subgroup G): subgroup G :=
subgroup.normal_closure {x | ∃ p q, p * q * p⁻¹ * q⁻¹ = x}

def general_commutator:subgroup G:=subgroup.closure{x|∃ p q,p∈ H₁ ∧ q∈ H₂ ∧  p * q * p⁻¹ * q⁻¹ = x}

--lemma equivalence : commutator = general_commutator ((subgroup G).has_top)(⊤: subgroup G ) :=sorry



/-- The abelianization of G is the quotient of G by its commutator subgroup -/
def abelianization : Type u :=
quotient_group.quotient (commutator G)

namespace abelianization

local attribute [instance] quotient_group.left_rel

instance : comm_group (abelianization G) :=
{ mul_comm := λ x y, quotient.induction_on₂' x y $ λ a b,
  begin
    apply quotient.sound,
    apply subgroup.subset_normal_closure,
    use b⁻¹, use a⁻¹,
    group,
  end,
.. quotient_group.quotient.group _ }

instance : inhabited (abelianization G) := ⟨1⟩

variable {G}

/-- `of` is the canonical projection from G to its abelianization. -/
def of : G →* abelianization G :=
{ to_fun := quotient_group.mk,
  map_one' := rfl,
  map_mul' := λ x y, rfl }

section lift
-- so far -- built Gᵃᵇ and proved it's an abelian group.
-- defined `of : G → Gᵃᵇ`

-- let A be an abelian group and let f be a group hom from G to A
variables {A : Type v} [comm_group A] (f : G →* A)

lemma commutator_subset_ker : commutator G ≤ f.ker :=
begin
  apply subgroup.normal_closure_le_normal,
  rintros x ⟨p, q, rfl⟩,
  simp [monoid_hom.mem_ker, mul_right_comm (f p) (f q)],
end

/-- If `f : G → A` is a group homomorphism to an abelian group, then `lift f` is the unique map from
  the abelianization of a `G` to `A` that factors through `f`. -/
def lift : abelianization G →* A :=
quotient_group.lift _ f (λ x h, f.mem_ker.2 $ commutator_subset_ker _ h)

@[simp] lemma lift.of (x : G) : lift f (of x) = f x :=
rfl

theorem lift.unique
  (φ : abelianization G →* A)
  -- hφ : φ agrees with f on the image of G in Gᵃᵇ
  (hφ : ∀ (x : G), φ (of x) = f x)
  {x : abelianization G} :
  φ x = lift f x :=
quotient_group.induction_on x hφ

end lift

variables {A : Type v} [monoid A]

theorem hom_ext (φ ψ : abelianization G →* A)
  (h : φ.comp of = ψ.comp of) : φ = ψ :=
begin
  ext x,
  apply quotient_group.induction_on x,
  intro z,
  show φ.comp of z = _,
  rw h,
  refl,
end

end abelianization
