import Atoms.Molecule.RegularComplex.Comap
import Atoms.Molecule.RegularComplex.OntoAtom
import Atoms.Molecule.Construction.SimplexMaps
import Mathlib.CategoryTheory.Core

universe u v

open CategoryTheory Order Set

namespace Atoms.Molecule.OGP

variable {P : OGP.{u}} {Q : OGP.{v}}

theorem IsMap.isMorphism_iff_grade_eq {f : P → Q} (hf : IsMap f) :
    IsMorphism f ↔ ∀ x, grade ℕ (f x) = grade ℕ x :=
  ⟨fun h => h.grade_eq, hf.isMorphism_of_grade_eq⟩

theorem IsMap.isMorphism_and_bijective_of_isComap {c : P → Q} (hQ : IsRDC Q) (hm : IsMap c)
    (hc : IsComap c) : IsMorphism c ∧ Function.Bijective c := by
  have hmor : IsMorphism c :=
    hm.isMorphism_of_grade_eq fun x => le_antisymm (hm.grade_le x) (hc.grade_le x)
  refine ⟨hmor, fun x x' h => ?_, hc.surjective⟩
  have hV : Q.IsAtomIn (LowerSet.Iic (c x)) :=
    (hQ (c x)).isAtomIn_Iic (LowerSet.mem_Iic_iff.2 le_rfl)
  refine hmor.injOn_of_isMoleculeIn_of_isAtomIn (hc.isMoleculeIn_Iic (c x)) hV
    (fun y ⟨z, hz, hzy⟩ => hzy ▸ hz) (hc.krullDim_lowerPreimage_Iic (c x)) ?_ ?_ h
  · exact (mem_lowerPreimage hc.monotone).2 (LowerSet.mem_Iic_iff.2 le_rfl)
  · exact (mem_lowerPreimage hc.monotone).2 (LowerSet.mem_Iic_iff.2 h.ge)

theorem IsComap.isMorphism_of_injective {c : P → Q} (hc : IsComap c) (hi : Function.Injective c) :
    IsMorphism c := by
  refine hc.isMorphism_of_lowerPreimage_Iic ⟨hi, hc.surjective⟩ fun x =>
    SetLike.ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩
  · obtain ⟨w, hzw, hw⟩ := (hc.isMoleculeIn_Iic (c x)).exists_le_maximal hz
    have hwx : c w ≤ c x := LowerSet.mem_Iic_iff.1 ((mem_lowerPreimage hc.monotone).1 hw.1)
    rcases lt_or_ge (grade ℕ (c w)) (grade ℕ (c x)) with hlt | hge
    · exact absurd (hc.grade_lt_of_mem_inf_boundary_lowerPreimage_Iic
        ((hc.grade_le w).trans_lt hlt) ⟨mem_boundary_of_maximal_of_grade_le hw le_rfl false,
          mem_boundary_of_maximal_of_grade_le hw le_rfl true⟩) (lt_irrefl _)
    · exact LowerSet.mem_Iic_iff.2 (hzw.trans (hi (GradeOrder.eq_of_le_of_grade_le hwx hge)).le)
  · exact (mem_lowerPreimage hc.monotone).2
      (LowerSet.mem_Iic_iff.2 (hc.monotone (LowerSet.mem_Iic_iff.1 hz)))

theorem IsMorphism.of_inverse {f : P → Q} {g : Q → P} (hf : IsMorphism f)
    (hgf : Function.LeftInverse g f) (hfg : Function.RightInverse g f) : IsMorphism g :=
  ⟨fun y α => by
    have h := hf.bijOn_faces (g y) α
    rw [hfg y] at h
    exact h.symm ⟨fun z _ => hfg z, fun x _ => hgf x⟩⟩

theorem IsMap.isComap_of_inverse {f : P → Q} {g : Q → P} (hP : IsRDC P) (hf : IsMap f)
    (hg : IsMap g) (hgf : Function.LeftInverse g f) (hfg : Function.RightInverse g f) :
    IsComap f := by
  have hIic (y : Q) : lowerPreimage hf.monotone (.Iic y) = .Iic (g y) :=
    SetLike.ext fun z => by
      rw [mem_lowerPreimage, LowerSet.mem_Iic_iff, LowerSet.mem_Iic_iff]
      exact ⟨fun h => (hgf z).ge.trans (hg.monotone h), fun h => (hf.monotone h).trans (hfg y).le⟩
  refine ⟨hf.monotone, fun y => by rw [hIic]; exact hP (g y), fun y n α => ?_⟩
  rw [hIic]
  refine SetLike.ext fun z => ⟨fun h => ?_, fun h => ?_⟩
  · have h' := (hg.finalOn y n α).1 ((mem_lowerPreimage hf.monotone).1 h)
    rwa [hgf z] at h'
  · have h' := (hf.finalOn (g y) n α).1 h
    rw [hfg y] at h'
    exact (mem_lowerPreimage hf.monotone).2 h'

theorem IsMorphism.isMap_and_isComap_of_bijective {f : P → Q} (hP : IsRDC P) (hQ : IsRDC Q)
    (hf : IsMorphism f) (hb : Function.Bijective f) :
    IsMap f ∧ IsComap f ∧ IsMap (Function.surjInv hb.2) ∧
      IsComap (Function.surjInv hb.2) := by
  have hgf := Function.leftInverse_surjInv hb
  have hfg := Function.rightInverse_surjInv hb.2
  have hm := hf.isMap_of_isRDC hP hQ
  have hm' := (hf.of_inverse hgf hfg).isMap_of_isRDC hQ hP
  exact ⟨hm, hm.isComap_of_inverse hP hm' hgf hfg, hm', hm'.isComap_of_inverse hQ hm hfg hgf⟩

theorem tfae_isMap_isComap (hP : IsRDC P) (hQ : IsRDC Q) (f : P → Q) :
    List.TFAE
      [IsMap f ∧ IsComap f,
       ∃ g : Q → P, IsMap f ∧ IsMap g ∧ Function.LeftInverse g f ∧ Function.RightInverse g f,
       ∃ g : Q → P, IsComap f ∧ IsComap g ∧ Function.LeftInverse g f ∧
         Function.RightInverse g f,
       IsMorphism f ∧ Function.Bijective f] := by
  tfae_have 1 → 4 := fun h => h.1.isMorphism_and_bijective_of_isComap hQ h.2
  tfae_have 4 → 1 := fun ⟨hf, hb⟩ => by
    obtain ⟨h1, h2, -, -⟩ := hf.isMap_and_isComap_of_bijective hP hQ hb
    exact ⟨h1, h2⟩
  tfae_have 4 → 2 := fun ⟨hf, hb⟩ => by
    obtain ⟨h1, -, h3, -⟩ := hf.isMap_and_isComap_of_bijective hP hQ hb
    exact ⟨_, h1, h3, Function.leftInverse_surjInv hb, Function.rightInverse_surjInv hb.2⟩
  tfae_have 4 → 3 := fun ⟨hf, hb⟩ => by
    obtain ⟨-, h2, -, h4⟩ := hf.isMap_and_isComap_of_bijective hP hQ hb
    exact ⟨_, h2, h4, Function.leftInverse_surjInv hb, Function.rightInverse_surjInv hb.2⟩
  tfae_have 2 → 4 := fun ⟨g, hf, hg, hgf, hfg⟩ => by
    refine ⟨hf.isMorphism_of_grade_eq fun x => le_antisymm (hf.grade_le x) ?_,
      hgf.injective, hfg.surjective⟩
    have := hg.grade_le (f x)
    rwa [hgf x] at this
  tfae_have 3 → 4 := fun ⟨g, hf, hg, hgf, hfg⟩ =>
    ⟨hf.isMorphism_of_inverse hg hgf hfg, hgf.injective, hfg.surjective⟩
  tfae_finish

namespace RDCpxDown

variable {P Q : RDCpxDown.{u}}

def isoOfIso (e : P.toOGP ≅ Q.toOGP) : P ≅ Q where
  hom := ConcreteCategory.ofHom (X := P) (Y := Q)
    ⟨e.hom, (isMorphism e.hom).isMap_of_isRDC P.isRDC Q.isRDC⟩
  inv := ConcreteCategory.ofHom (X := Q) (Y := P)
    ⟨e.inv, (isMorphism e.inv).isMap_of_isRDC Q.isRDC P.isRDC⟩
  hom_inv_id := ConcreteCategory.hom_ext _ _ fun x => Iso.hom_inv_id_apply e x
  inv_hom_id := ConcreteCategory.hom_ext _ _ fun x => Iso.inv_hom_id_apply e x

@[simp] theorem isoOfIso_hom_apply (e : P.toOGP ≅ Q.toOGP) (x : P.toOGP) :
    ConcreteCategory.hom (isoOfIso e).hom x = e.hom x :=
  rfl

theorem exists_iso_of_bijective (f : P ⟶ Q) (hb : Function.Bijective (ConcreteCategory.hom f)) :
    ∃ e : P.toOGP ≅ Q.toOGP, ∀ x, e.hom x = ConcreteCategory.hom f x := by
  have hmor := (ConcreteCategory.hom f).isMap.isMorphism_of_injective hb.1
  let g : P.toOGP ⟶ Q.toOGP := ConcreteCategory.ofHom ⟨ConcreteCategory.hom f, hmor⟩
  have : IsIso g := (isIso_iff_bijective g).2 hb
  exact ⟨asIso g, fun _ => rfl⟩

theorem isIso_iff_bijective (f : P ⟶ Q) :
    IsIso f ↔ Function.Bijective (ConcreteCategory.hom f) := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun hb => ?_⟩
  · exact Function.LeftInverse.injective (g := ConcreteCategory.hom (inv f)) fun x =>
      ConcreteCategory.congr_hom (IsIso.hom_inv_id f) x
  · exact Function.RightInverse.surjective (g := ConcreteCategory.hom (inv f)) fun x =>
      ConcreteCategory.congr_hom (IsIso.inv_hom_id f) x
  · obtain ⟨e, he⟩ := exists_iso_of_bijective f hb
    have : f = (isoOfIso e).hom := ConcreteCategory.hom_ext _ _ fun x => (he x).symm
    rw [this]
    infer_instance

theorem isIso_of_isComap (f : P ⟶ Q) (hc : IsComap (ConcreteCategory.hom f)) : IsIso f :=
  (isIso_iff_bijective f).2
    (IsMap.isMorphism_and_bijective_of_isComap Q.isRDC (ConcreteCategory.hom f).isMap hc).2

end RDCpxDown

namespace RDCpxUp

variable {P Q : RDCpxUp.{u}}

def isoOfIso (e : P.toOGP ≅ Q.toOGP) : P ≅ Q where
  hom := ConcreteCategory.ofHom (X := P) (Y := Q) ⟨e.hom, isComap_iso e Q.isRDC⟩
  inv := ConcreteCategory.ofHom (X := Q) (Y := P) ⟨e.inv, isComap_iso e.symm P.isRDC⟩
  hom_inv_id := ConcreteCategory.hom_ext _ _ fun x => Iso.hom_inv_id_apply e x
  inv_hom_id := ConcreteCategory.hom_ext _ _ fun x => Iso.inv_hom_id_apply e x

@[simp] theorem isoOfIso_hom_apply (e : P.toOGP ≅ Q.toOGP) (x : P.toOGP) :
    ConcreteCategory.hom (isoOfIso e).hom x = e.hom x :=
  rfl

theorem isIso_iff_bijective (f : P ⟶ Q) :
    IsIso f ↔ Function.Bijective (ConcreteCategory.hom f) := by
  refine ⟨fun _ => ConcreteCategory.bijective_of_isIso f, fun hb => ?_⟩
  let g : P.toOGP ⟶ Q.toOGP := ConcreteCategory.ofHom
    ⟨ConcreteCategory.hom f, (ConcreteCategory.hom f).isComap.isMorphism_of_injective hb.1⟩
  have : IsIso g := (OGP.isIso_iff_bijective g).2 hb
  have hf : f = (isoOfIso (asIso g)).hom := ConcreteCategory.hom_ext _ _ fun _ => rfl
  rw [hf]
  infer_instance

end RDCpxUp

theorem RDCpx.isIso_iff {P Q : RDCpx.{u}} (f : P ⟶ Q) : IsIso f ↔ IsIso f.hom := by
  refine ⟨fun h => (wideSubcategoryInclusion _).map_isIso f, fun h => ?_⟩
  obtain ⟨e, he⟩ := RDCpxDown.exists_iso_of_bijective f.hom
    ((RDCpxDown.isIso_iff_bijective _).1 h)
  have : f = (RDCpx.isoOfIso e).hom :=
    WideSubcategory.hom_ext _ (ConcreteCategory.hom_ext _ _ fun x => (he x).symm)
  rw [this]
  infer_instance

theorem RDCpxEq.isIso_iff {P Q : RDCpxEq.{u}} (f : P ⟶ Q) :
    IsIso f ↔ IsIso (RDCpxEq.toRDCpx.map f).hom := by
  refine ⟨fun h => (wideSubcategoryInclusion _).map_isIso (RDCpxEq.toRDCpx.map f), fun h => ?_⟩
  obtain ⟨e, he⟩ := RDCpxDown.exists_iso_of_bijective f.hom
    ((RDCpxDown.isIso_iff_bijective _).1 h)
  let hP := P.obj.isRDC
  let hQ := Q.obj.isRDC
  let i : P ≅ Q := WideSubcategory.isoMk (RDCpxDown.isoOfIso e)
    ((isMorphism e.hom).isLocalEmbedding_of_isRDC hP hQ)
    ((isMorphism e.inv).isLocalEmbedding_of_isRDC hQ hP)
  have : f = i.hom :=
    WideSubcategory.hom_ext _ (ConcreteCategory.hom_ext _ _ fun x => (he x).symm)
  rw [this]
  infer_instance

namespace RDCpxDown

variable {P Q : RDCpxDown.{u}}

def ogpIso (i : P ≅ Q) : P.toOGP ≅ Q.toOGP :=
  have hg (x : P.toOGP) : grade ℕ (ConcreteCategory.hom i.hom x) = grade ℕ x :=
    le_antisymm ((ConcreteCategory.hom i.hom).isMap.grade_le x) (by
      have := (ConcreteCategory.hom i.inv).isMap.grade_le (ConcreteCategory.hom i.hom x)
      refine le_trans (le_of_eq ?_) this
      exact (congrArg (grade ℕ) (ConcreteCategory.congr_hom i.hom_inv_id x)).symm)
  have hg' (y : Q.toOGP) : grade ℕ (ConcreteCategory.hom i.inv y) = grade ℕ y :=
    le_antisymm ((ConcreteCategory.hom i.inv).isMap.grade_le y) (by
      have := (ConcreteCategory.hom i.hom).isMap.grade_le (ConcreteCategory.hom i.inv y)
      refine le_trans (le_of_eq ?_) this
      exact (congrArg (grade ℕ) (ConcreteCategory.congr_hom i.inv_hom_id y)).symm)
  { hom := ConcreteCategory.ofHom ⟨ConcreteCategory.hom i.hom,
      (ConcreteCategory.hom i.hom).isMap.isMorphism_of_grade_eq hg⟩
    inv := ConcreteCategory.ofHom ⟨ConcreteCategory.hom i.inv,
      (ConcreteCategory.hom i.inv).isMap.isMorphism_of_grade_eq hg'⟩
    hom_inv_id := by ext x; exact ConcreteCategory.congr_hom i.hom_inv_id x
    inv_hom_id := by ext x; exact ConcreteCategory.congr_hom i.inv_hom_id x }

end RDCpxDown

namespace RDCpxUp

variable {P Q : RDCpxUp.{u}}

def ogpIso (i : P ≅ Q) : P.toOGP ≅ Q.toOGP where
  hom := ConcreteCategory.ofHom ⟨ConcreteCategory.hom i.hom,
    (ConcreteCategory.hom i.hom).isComap.isMorphism_of_inverse (ConcreteCategory.hom i.inv).isComap
      (fun x => ConcreteCategory.congr_hom i.hom_inv_id x)
      (fun x => ConcreteCategory.congr_hom i.inv_hom_id x)⟩
  inv := ConcreteCategory.ofHom ⟨ConcreteCategory.hom i.inv,
    (ConcreteCategory.hom i.inv).isComap.isMorphism_of_inverse (ConcreteCategory.hom i.hom).isComap
      (fun x => ConcreteCategory.congr_hom i.inv_hom_id x)
      (fun x => ConcreteCategory.congr_hom i.hom_inv_id x)⟩
  hom_inv_id := by ext x; exact ConcreteCategory.congr_hom i.hom_inv_id x
  inv_hom_id := by ext x; exact ConcreteCategory.congr_hom i.inv_hom_id x

end RDCpxUp

namespace RDCpxDown

def coreDownToUp : Core RDCpxDown.{u} ⥤ Core RDCpxUp.{u} where
  obj P := ⟨P.of⟩
  map f := ⟨RDCpxUp.isoOfIso (ogpIso f.iso)⟩
  map_id _ := Core.hom_ext (ConcreteCategory.hom_ext _ _ fun _ => rfl)
  map_comp _ _ := Core.hom_ext (ConcreteCategory.hom_ext _ _ fun _ => rfl)

def coreUpToDown : Core RDCpxUp.{u} ⥤ Core RDCpxDown.{u} where
  obj P := ⟨P.of⟩
  map f := ⟨isoOfIso (RDCpxUp.ogpIso f.iso)⟩
  map_id _ := Core.hom_ext (ConcreteCategory.hom_ext _ _ fun _ => rfl)
  map_comp _ _ := Core.hom_ext (ConcreteCategory.hom_ext _ _ fun _ => rfl)

def coreDownEquivUp : Core RDCpxDown.{u} ≌ Core RDCpxUp.{u} where
  functor := coreDownToUp
  inverse := coreUpToDown
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
    (fun _ => Core.hom_ext (ConcreteCategory.hom_ext _ _ fun _ => rfl))
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)
    (fun _ => Core.hom_ext (ConcreteCategory.hom_ext _ _ fun _ => rfl))

theorem coreDownEquivUp_functor_map_hom_apply {P Q : Core RDCpxDown.{u}} (f : P ⟶ Q)
    (x : P.of.toOGP) :
    ConcreteCategory.hom (coreDownEquivUp.functor.map f).iso.hom x =
      ConcreteCategory.hom f.iso.hom x :=
  rfl

end RDCpxDown

namespace RDCpxDown

def pointIsTerminal : Limits.IsTerminal (RDCpxDown.mk point.{u}
    (isRDC_of_isMolecule isAtom_point.isMoleculeIn)) :=
  Limits.IsTerminal.ofUniqueHom
    (fun Y => ConcreteCategory.ofHom (X := Y) (Y := RDCpxDown.mk point.{u}
      (isRDC_of_isMolecule isAtom_point.isMoleculeIn))
      ⟨fun _ => ⊤, isMap_constPoint Y.isRDC⟩)
    (fun _ _ => ConcreteCategory.hom_ext _ _ fun _ => le_antisymm le_top (isMin_point _ le_top))

end RDCpxDown

end Atoms.Molecule.OGP
