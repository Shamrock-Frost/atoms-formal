import Atoms.Molecule.RegularComplex.Basic
import Atoms.Molecule.Transport

universe u v w

open CategoryTheory Order Set Topology

namespace Atoms.Molecule.OGP

variable {P : OGP.{u}} {Q : OGP.{v}}

namespace IsMap

variable {f : P → Q} (hf : IsMap f)
include hf

theorem exists_mem_faces_apply_eq {x : P} (h : grade ℕ (f x) < grade ℕ x) (α : Bool) :
    ∃ y ∈ P.faces α x, f y = f x := by
  obtain ⟨n, hn⟩ : ∃ n, grade ℕ x = n + 1 := ⟨grade ℕ x - 1, by omega⟩
  have hb : Q.boundary (.Iic (f x)) n α = .Iic (f x) :=
    boundary_eq_self (by rw [LowerSet.krullDim_Iic, Nat.cast_le]; omega) α
  have hx : f x ∈ f '' P.boundary (.Iic x) n α := by
    rw [hf.image_boundary, hb]
    exact LowerSet.mem_Iic_iff.2 le_rfl
  obtain ⟨w, hw, hwx⟩ := hx
  rw [boundary_Iic hn] at hw
  obtain ⟨y, hy, hwy⟩ := mem_lowerClosure.1 hw
  exact ⟨y, hy, le_antisymm (hf.monotone hy.1.le) (hwx ▸ hf.monotone hwy)⟩

theorem exists_le_apply_eq (x : P) : ∃ y ≤ x, f y = f x ∧ grade ℕ y = grade ℕ (f x) := by
  have hb : Q.boundary (.Iic (f x)) (grade ℕ (f x)) true = .Iic (f x) :=
    boundary_eq_self (by rw [LowerSet.krullDim_Iic]) true
  have hx : f x ∈ f '' P.boundary (.Iic x) (grade ℕ (f x)) true := by
    rw [hf.image_boundary, hb]
    exact LowerSet.mem_Iic_iff.2 le_rfl
  obtain ⟨y, hy, hyx⟩ := hx
  refine ⟨y, boundary_le _ _ _ hy, hyx, le_antisymm (grade_le_of_mem_boundary hy) ?_⟩
  rw [← hyx]
  exact hf.grade_le y

theorem minimal_fibre_iff (z : P) :
    Minimal (fun w => f w = f z) z ↔ grade ℕ z = grade ℕ (f z) := by
  refine ⟨fun hmin => ?_, fun hd => ⟨rfl, fun w hw hwz => ?_⟩⟩
  · obtain ⟨y, hyz, hy, hd⟩ := hf.exists_le_apply_eq z
    obtain rfl := le_antisymm hyz (hmin.2 hy hyz)
    exact hd
  · refine (GradeOrder.eq_of_le_of_grade_le hwz ?_).ge
    rw [hd, ← hw]
    exact hf.grade_le w

theorem existsUnique_mem_boundary_apply_eq (x : P) (α : Bool) :
    ∃! y, y ∈ P.boundary (.Iic x) (grade ℕ (f x)) α ∧ grade ℕ y = grade ℕ (f x) ∧ f y = f x := by
  have hb : Q.boundary (.Iic (f x)) (grade ℕ (f x)) α = .Iic (f x) :=
    boundary_eq_self (by rw [LowerSet.krullDim_Iic]) α
  have hfx : f x ∈ (Q.boundary (.Iic (f x)) (grade ℕ (f x)) α : Set Q) := by
    rw [hb]
    exact LowerSet.mem_Iic_iff.2 le_rfl
  have hmem {w : P} (hw : w ∈ P.boundary (.Iic x) (grade ℕ (f x)) α) (hfw : f x ≤ f w) :
      grade ℕ w = grade ℕ (f x) ∧ f w = f x := by
    have hwx : f w = f x := le_antisymm (hf.monotone (boundary_le _ _ _ hw)) hfw
    exact ⟨le_antisymm (grade_le_of_mem_boundary hw) (hwx ▸ hf.grade_le w), hwx⟩
  obtain ⟨y, hy, hyx⟩ := (hf.image_boundary x _ α).symm ▸ hfx
  refine ⟨y, ⟨hy, hmem hy hyx.ge⟩, fun z ⟨hz, hgz, hzx⟩ => ?_⟩
  exact IsUpperSet.subsingleton_of_isPreconnected_of_grade_eq
    ((hf.finalOn x _ α).2 (f x) hfx).isPreconnected (fun w hw => (hmem hw.1 hw.2).1)
    ⟨hz, hzx.ge⟩ ⟨hy, hyx.ge⟩

end IsMap

theorem bijective_of_isAtom {P Q : OGP.{u}} (hP : P.IsAtom) (hQ : Q.IsAtom) {f : P → Q}
    (hf : IsMap f) [hf.monotone.functor.IsFibered] (hs : Function.Surjective f)
    (hd : krullDim P = krullDim Q) : Function.Bijective f := by
  obtain ⟨tP, htP⟩ := hP.exists_eq_Iic
  obtain ⟨tQ, htQ⟩ := hQ.exists_eq_Iic
  have hdim {R : OGP.{u}} {t : R} (ht : (⊤ : LowerSet R) = .Iic t) : krullDim R = grade ℕ t := by
    rw [← LowerSet.krullDim_top, ht, LowerSet.krullDim_Iic]
  have hP' : IsTop tP := fun z => (htP ▸ LowerSet.mem_top : z ∈ LowerSet.Iic tP)
  have hQ' : IsTop tQ := fun z => (htQ ▸ LowerSet.mem_top : z ∈ LowerSet.Iic tQ)
  obtain ⟨u, rfl⟩ := hs tQ
  have htop : f tP = f u := le_antisymm (hQ' _) (hf.monotone (hP' u))
  have hdt : grade ℕ (f tP) = grade ℕ tP := by
    rw [htop]
    exact_mod_cast (hdim htQ).symm.trans (hd.symm.trans (hdim htP))
  exact ⟨hf.monotone.injective_of_grade_apply_eq hP'
    (hf.monotone.grade_apply_eq_of_isTop hP' hdt), hs⟩

theorem IsMap.injOn_Iic_and_grade_apply_eq {f : P → Q} (hf : IsMap f)
    [hf.monotone.functor.IsFibered] {y : P} (hy : grade ℕ (f y) = grade ℕ y) :
    Set.InjOn f (Set.Iic y) ∧ ∀ x ≤ y, grade ℕ (f x) = grade ℕ x := by
  have hι := isLocalEmbedding_of_isInclusion (incl (P := P) (.Iic y))
  have : hι.monotone.functor.IsFibered := hι.functor_isFibered
  have hg : (hf.monotone.comp hι.monotone).functor.IsFibered :=
    Monotone.functor_isFibered_comp hι.monotone hf.monotone
  have ht : IsTop (⟨y, LowerSet.mem_Iic_iff.2 le_rfl⟩ : P.restrict (.Iic y)) := fun z => z.2
  have hgr (z : P.restrict (.Iic y)) : grade ℕ z = grade ℕ z.1 :=
    ((isMorphism (incl (P := P) (.Iic y))).grade_eq z).symm
  have hd := (hf.monotone.comp hι.monotone).grade_apply_eq_of_isTop ht (by
    rw [hgr]
    exact hy)
  refine ⟨fun a ha b hb hab => ?_, fun x hx => (hd ⟨x, hx⟩).trans (hgr _)⟩
  exact congrArg Subtype.val ((hf.monotone.comp hι.monotone).injective_of_grade_apply_eq ht hd
    (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) hab)

theorem IsMap.of_comp {R S : OGP.{v}} {f : P → R} (g : R ⟶ S) [IsInclusion g]
    (h : IsMap (g ∘ f)) : IsMap f := by
  let e : R ↪o S := OrderEmbedding.ofMapLEIff g fun _ _ => IsInclusion.le_iff g
  refine ⟨IsUpperSet.isClosedMap_iff_fibration.2 fun x y hy => ?_, fun x n α => ?_⟩
  · obtain ⟨x', hx'x, hx'⟩ := h.fibration ((IsInclusion.le_iff g).2 hy)
    exact ⟨x', hx'x, IsInclusion.injective hx'⟩
  · have hfin := h.finalOn x n α
    rw [Function.comp_apply, ← map_Iic, ← map_boundary, coe_map] at hfin
    exact FinalOn.of_comp (g := e) hfin

theorem IsMap.codRestrict {f : P → Q} (hf : IsMap f) {C : LowerSet Q} (h : ∀ x, f x ∈ C) :
    IsMap (Q := Q.restrict C) fun x => ⟨f x, h x⟩ :=
  IsMap.of_comp (R := Q.restrict C) (incl C) hf

theorem IsMap.codRestrict_functor_isFibered {f : P → Q} (hf : IsMap f)
    [hf.monotone.functor.IsFibered] {C : LowerSet Q} (h : ∀ x, f x ∈ C) :
    (hf.codRestrict h).monotone.functor.IsFibered :=
  Monotone.functor_isFibered_of_comp _ (OrderEmbedding.subtype (· ∈ C))
    ‹hf.monotone.functor.IsFibered›

theorem IsRDC.restrict (hP : P.IsRDC) (U : LowerSet P) : (P.restrict U).IsRDC := fun x => by
  rw [← isMoleculeIn_map_iff (incl U), map_Iic, incl_apply]
  exact hP x.1

theorem IsAtomIn.isAtom_restrict {U : LowerSet P} (h : P.IsAtomIn U) : (P.restrict U).IsAtom := by
  obtain ⟨hm, t, rfl⟩ := h
  refine ⟨(isMolecule_restrict_iff _).2 hm, ⟨t, LowerSet.mem_Iic_iff.2 le_rfl⟩, ?_⟩
  exact SetLike.ext fun z => iff_of_true LowerSet.mem_top z.2

namespace RDCpx

abbrev restrict (P : RDCpx.{u}) (U : LowerSet P.obj.toOGP) : RDCpx.{u} :=
  ⟨⟨P.obj.toOGP.restrict U, P.obj.isRDC.restrict U⟩⟩

def restrictIncl (P : RDCpx.{u}) (U : LowerSet P.obj.toOGP) : restrict P U ⟶ P :=
  ofInclusion (incl U)

@[simp] theorem restrictIncl_apply (P : RDCpx.{u}) (U : LowerSet P.obj.toOGP)
    (x : (restrict P U).obj) : ConcreteCategory.hom (restrictIncl P U).hom x = x.1 :=
  rfl

def codRestrict {P Q : RDCpx.{u}} (f : P ⟶ Q) (C : LowerSet Q.obj.toOGP)
    (h : ∀ x, ConcreteCategory.hom f.hom x ∈ C) : P ⟶ restrict Q C :=
  letI : (ConcreteCategory.hom f.hom).isMap.monotone.functor.IsFibered := f.property
  ⟨ConcreteCategory.ofHom (X := P.obj) (Y := (restrict Q C).obj)
      ⟨_, (ConcreteCategory.hom f.hom).isMap.codRestrict h⟩,
    (ConcreteCategory.hom f.hom).isMap.codRestrict_functor_isFibered h⟩

@[reassoc (attr := simp)]
theorem codRestrict_restrictIncl {P Q : RDCpx.{u}} (f : P ⟶ Q) (C : LowerSet Q.obj.toOGP)
    (h : ∀ x, ConcreteCategory.hom f.hom x ∈ C) : codRestrict f C h ≫ restrictIncl Q C = f := by
  ext x
  rfl

def inclusion (P : RDCpx.{u}) {U V : LowerSet P.obj.toOGP} (h : U ≤ V) :
    restrict P U ⟶ restrict P V :=
  codRestrict (restrictIncl P U) V fun x => h x.2

@[reassoc (attr := simp)]
theorem inclusion_restrictIncl (P : RDCpx.{u}) {U V : LowerSet P.obj.toOGP} (h : U ≤ V) :
    inclusion P h ≫ restrictIncl P V = restrictIncl P U :=
  codRestrict_restrictIncl _ _ _

end RDCpx

end Atoms.Molecule.OGP
