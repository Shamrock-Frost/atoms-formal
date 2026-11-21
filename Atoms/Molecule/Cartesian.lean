import Atoms.ForMathlib.CategoryTheory.FiberedCategory.Preorder
import Atoms.ForMathlib.Order.Grade
import Atoms.ForMathlib.Topology.Order.UpperLowerSetTopology
import Atoms.Molecule.Boundary
import Atoms.Molecule.Inclusion

universe u v w

open CategoryTheory Order Set Topology

namespace Atoms.Molecule.OGP

variable {P : OGP.{u}} {Q : OGP.{v}} {R : OGP.{w}}

structure IsMap (f : P → Q) : Prop where
  isClosedMap : IsClosedMap f
  finalOn : ∀ (x : P) (n : ℕ) (α : Bool),
    FinalOn f (P.boundary (.Iic x) n α) (Q.boundary (.Iic (f x)) n α)

namespace IsMap

variable {f : P → Q} (hf : IsMap f)
include hf

theorem fibration : Relation.Fibration (· ≤ ·) (· ≤ ·) f :=
  IsUpperSet.isClosedMap_iff_fibration.1 hf.isClosedMap

theorem mapsTo_Iic (x : P) : MapsTo f (Iic x) (Iic (f x)) := fun y hy => by
  have hx : P.boundary (.Iic x) (grade ℕ x) true = .Iic x :=
    boundary_eq_self (by rw [LowerSet.krullDim_Iic]) true
  have h := (hf.finalOn x (grade ℕ x) true).1 (by rw [hx]; exact hy)
  exact boundary_le _ _ _ h

theorem monotone : Monotone f := fun _ x hy => hf.mapsTo_Iic x hy

theorem image_Iic (x : P) : f '' Iic x = Iic (f x) :=
  (Relation.fibration_iff_image_Iic hf.monotone).1 hf.fibration x

theorem grade_le (x : P) : grade ℕ (f x) ≤ grade ℕ x :=
  hf.fibration.grade_apply_le x

theorem image_boundary (x : P) (n : ℕ) (α : Bool) :
    f '' P.boundary (.Iic x) n α = Q.boundary (.Iic (f x)) n α :=
  ((hf.finalOn x n α).surjOn hf.fibration (LowerSet.lower _)).image_eq_of_mapsTo
    (hf.finalOn x n α).1

omit hf in
theorem id (P : OGP.{u}) : IsMap (id : P → P) :=
  ⟨IsClosedMap.id, fun _ _ _ => finalOn_id _⟩

omit hf in
theorem comp {f : P → Q} {g : Q → R} (hf : IsMap f) (hg : IsMap g) : IsMap (g ∘ f) :=
  ⟨hg.isClosedMap.comp hf.isClosedMap, fun x n α =>
    (hg.finalOn (f x) n α).comp (hf.finalOn x n α) hg.monotone⟩

end IsMap

theorem isMap_of_isInclusion {P Q : OGP.{u}} (f : P ⟶ Q) [IsInclusion f] : IsMap f := by
  refine ⟨(isMorphism f).isClosedMap, fun x n α => ⟨fun y hy => ?_, fun y hy => ?_⟩⟩
  · have h : f y ∈ map f (P.boundary (.Iic x) n α) := ⟨y, hy, rfl⟩
    rwa [map_boundary, map_Iic] at h
  · have hy' : y ∈ map f (P.boundary (.Iic x) n α) := by rwa [map_boundary, map_Iic]
    obtain ⟨y₀, hy₀, rfl⟩ := hy'
    exact ⟨⟨y₀, hy₀, le_rfl⟩, IsUpperSet.isPreconnected_of_isLeast
      ⟨⟨hy₀, le_rfl⟩, fun _ hc => (IsInclusion.le_iff f).1 hc.2⟩⟩

namespace IsLocalEmbedding

variable {f : P → Q} {g : Q → R}

theorem monotone (hf : IsLocalEmbedding f) : Monotone f := fun y x hyx => by
  have hy : y ∈ closure ({x} : Set P) := by rw [IsUpperSet.closure_singleton]; exact hyx
  have hx : x ∈ closure ({x} : Set P) := subset_closure rfl
  exact IsUpperSet.monotone_iff_continuous.2 (hf x).continuous
    (show (⟨y, hy⟩ : closure ({x} : Set P)) ≤ ⟨x, hx⟩ from hyx)

theorem id (P : OGP.{u}) : IsLocalEmbedding (id : P → P) := fun _ =>
  isClosed_closure.isClosedEmbedding_subtypeVal

theorem comp (hg : IsLocalEmbedding g) (hf : IsLocalEmbedding f) : IsLocalEmbedding (g ∘ f) :=
  fun x => by
    have hmaps (y : closure ({x} : Set P)) : f y ∈ closure ({f x} : Set Q) :=
      (Set.ext_iff.1 IsUpperSet.closure_singleton _).2
        (hf.monotone ((Set.ext_iff.1 IsUpperSet.closure_singleton (y : P)).1 y.2))
    have h : IsClosedEmbedding ((closure ({f x} : Set Q)).codRestrict
        ((closure ({x} : Set P)).domRestrict f) hmaps) :=
      .of_isEmbedding_isClosedMap ((hf x).isEmbedding.codRestrict _ _)
        ((hf x).isClosedMap.codRestrict _)
    exact (hg (f x)).comp h

theorem functor_isFibered (hf : IsLocalEmbedding f) : hf.monotone.functor.IsFibered := by
  refine (Monotone.functor_isFibered_iff _).2 fun x y hy => ?_
  obtain ⟨y', hy'x, rfl⟩ := IsUpperSet.isClosedMap_iff_fibration.1 hf.isClosedMap hy
  refine ⟨y', hy'x, rfl, fun z hzx hzy => ?_⟩
  have hmem {c : P} (hc : c ≤ x) : c ∈ closure ({x} : Set P) := by
    rw [IsUpperSet.closure_singleton]; exact hc
  have hsp : (⟨y', hmem hy'x⟩ : closure ({x} : Set P)) ⤳ ⟨z, hmem hzx⟩ :=
    (hf x).isInducing.specializes_iff.1 (IsUpperSet.specializes_iff_le.2 hzy)
  exact (IsUpperSet.specializes_iff_le (α := closure ({x} : Set P))).1 hsp

end IsLocalEmbedding

theorem isLocalEmbedding_of_isInclusion {P Q : OGP.{u}} (f : P ⟶ Q) [IsInclusion f] :
    IsLocalEmbedding f := fun _ =>
  (IsInclusion.isClosedEmbedding f).comp isClosed_closure.isClosedEmbedding_subtypeVal

end Atoms.Molecule.OGP
