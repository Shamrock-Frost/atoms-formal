import Atoms.Molecule.ClosedEmbedding
import Atoms.Molecule.MoleculeShape.Basic
import Atoms.Molecule.RegularComplex.Morphism
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.InducedCategory
import Mathlib.Data.Fintype.Basic

open CategoryTheory Order Atoms.Molecule Atoms.Molecule.OGP

namespace Atoms.Shape

structure Atom extends MoleculeShape where
  exists_top : ∃ t : toFiniteOGP.ogp, (⊤ : LowerSet toFiniteOGP.ogp) = LowerSet.Iic t

namespace Atom

instance : CoeSort Atom Type := ⟨fun U => U.ogp⟩

theorem isAtom (U : Atom) : IsAtom U.ogp := ⟨U.isMolecule, U.exists_top⟩

theorem isRDC (U : Atom) : IsRDC U.ogp := isRDC_of_isMolecule U.isMolecule

@[implicit_reducible] def ofIsAtom (P : FiniteOGP) (hP : IsAtom P.ogp) : Atom := ⟨⟨P, hP.1⟩, hP.2⟩

@[simp] theorem toFiniteOGP_ofIsAtom (P : FiniteOGP) (hP : IsAtom P.ogp) :
    (ofIsAtom P hP).toFiniteOGP = P :=
  rfl

def toRoundShape (U : Atom) : RoundShape := ⟨U.toMoleculeShape, U.isAtom.isRound⟩

@[ext] theorem ext {U V : Atom} (h : U.toFiniteOGP = V.toFiniteOGP) : U = V := by
  obtain ⟨⟨P, _⟩, _⟩ := U
  obtain ⟨⟨Q, _⟩, _⟩ := V
  cases h
  rfl

instance instDecidableEqAtom : DecidableEq Atom := fun U V =>
  decidable_of_iff (U.toFiniteOGP = V.toFiniteOGP)
    ⟨Atom.ext, congrArg fun W : Atom => W.toFiniteOGP⟩

def ofShapeData? (d : ShapeData) : Option Atom :=
  if hv : d.Valid then
    let P : FiniteOGP := ⟨d, hv⟩
    if ha : IsAtom P.ogp then some (ofIsAtom P ha) else none
  else none

@[simp] theorem ofShapeData?_data (U : Atom) : ofShapeData? U.data = some U := by
  rcases U with ⟨⟨⟨d, hv⟩, hm⟩, ht⟩
  have ha : IsAtom (FiniteOGP.ogp ⟨d, hv⟩) := ⟨hm, ht⟩
  simp [ofShapeData?, hv, ha, ofIsAtom]

theorem data_of_ofShapeData? {d : ShapeData} {U : Atom}
    (h : ofShapeData? d = some U) : U.data = d := by
  dsimp only [ofShapeData?] at h
  split at h <;> [(split at h <;> cases h; rfl); cases h]

end Atom

instance categoryAtom : SmallCategory Atom :=
  inferInstanceAs (Category (InducedCategory RDCpx.{0} fun U : Atom => U.rdc))

instance instFunLikeHom (U V : Atom) :
    FunLike (InducedCategory.Hom (F := fun W : Atom => W.rdc) U V) U.ogp V.ogp where
  coe f := ConcreteCategory.hom f.hom.hom
  coe_injective _ _ h :=
    InducedCategory.Hom.ext (WideSubcategory.hom_ext _ (ConcreteCategory.coe_ext h))

instance : ConcreteCategory Atom (InducedCategory.Hom (F := fun W : Atom => W.rdc)) where
  hom f := f
  ofHom f := f

abbrev atomToRDCpx : Atom ⥤ RDCpx.{0} :=
  inducedFunctor fun U : Atom => U.rdc

def Atom.fullyFaithful : atomToRDCpx.FullyFaithful :=
  fullyFaithfulInducedFunctor fun U : Atom => U.rdc

namespace Atom

variable {U V W : Atom}

def homMk (f : U.ogp → V.ogp) (hf : IsMap f) [hfib : hf.monotone.functor.IsFibered] : U ⟶ V :=
  InducedCategory.homMk ⟨ConcreteCategory.ofHom (X := U.rdc.obj) (Y := V.rdc.obj) ⟨f, hf⟩, hfib⟩

@[simp] theorem homMk_apply (f : U.ogp → V.ogp) (hf : IsMap f) [hf.monotone.functor.IsFibered]
    (x : U.ogp) : homMk f hf x = f x :=
  rfl

theorem isMap (f : U ⟶ V) : IsMap (f : U.ogp → V.ogp) :=
  (ConcreteCategory.hom f.hom.hom).isMap

instance functor_isFibered (f : U ⟶ V) : (isMap f).monotone.functor.IsFibered :=
  f.hom.property

@[ext] theorem hom_ext {f g : U ⟶ V} (h : ∀ x : U.ogp, f x = g x) : f = g :=
  ConcreteCategory.hom_ext f g h

def ofInclusion (f : U.ogp ⟶ V.ogp) [hf : IsInclusion f] : U ⟶ V :=
  InducedCategory.homMk (@RDCpx.ofInclusion U.rdc V.rdc f hf)

@[simp] theorem ofInclusion_apply (f : U.ogp ⟶ V.ogp) [IsInclusion f] (x : U.ogp) :
    ofInclusion (U := U) (V := V) f x = f x :=
  rfl

@[simps!] def isoOfIso (e : U.ogp ≅ V.ogp) : U ≅ V :=
  InducedCategory.isoMk (RDCpx.isoOfIso (P := U.rdc) (Q := V.rdc) e)

end Atom

instance decidableEqHom (U V : Atom) : DecidableEq (U ⟶ V) := fun f g =>
  decidable_of_iff ((f : U.ogp → V.ogp) = g)
    ⟨ConcreteCategory.coe_ext, congrArg (fun h : U ⟶ V => (h : U.ogp → V.ogp))⟩

instance fintypeHom (U V : Atom) : Fintype (U ⟶ V) :=
  Fintype.ofEquiv {f : U.ogp → V.ogp // ∃ hf : IsMap f, hf.monotone.functor.IsFibered}
    { toFun := fun ⟨f, hf⟩ =>
        letI : hf.1.monotone.functor.IsFibered := hf.2
        Atom.homMk f hf.1
      invFun := fun f => ⟨f, Atom.isMap f, Atom.functor_isFibered f⟩
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun _ => rfl }

abbrev IsInclusionHom {U V : Atom} (f : U ⟶ V) : Prop :=
  Function.Injective f

abbrev IsCollapseHom {U V : Atom} (f : U ⟶ V) : Prop :=
  Function.Surjective f

instance decidableIsInclusionHom {U V : Atom} (f : U ⟶ V) : Decidable (IsInclusionHom f) :=
  inferInstanceAs (Decidable (Function.Injective f))

instance decidableIsCollapseHom {U V : Atom} (f : U ⟶ V) : Decidable (IsCollapseHom f) :=
  inferInstanceAs (Decidable (Function.Surjective f))

abbrev inclusions : MorphismProperty Atom :=
  MorphismProperty.injective Atom

abbrev collapses : MorphismProperty Atom :=
  MorphismProperty.surjective Atom

theorem mono_of_isInclusionHom {U V : Atom} (f : U ⟶ V) (hf : IsInclusionHom f) : Mono f :=
  ConcreteCategory.mono_of_injective f hf

theorem Atom.isMorphism_of_isInclusionHom {U V : Atom} (f : U ⟶ V) (hf : IsInclusionHom f) :
    IsMorphism (f : U.ogp → V.ogp) :=
  (Atom.isMap f).isMorphism_of_injective hf

def Atom.conjHom {P Q : OGP.{0}} {U V : Atom} (eU : P ≅ U.ogp) (eV : Q ≅ V.ogp)
    (g : P → Q) (hg : IsMap g) [hg.monotone.functor.IsFibered] : U ⟶ V :=
  letI := (isLocalEmbedding_of_isInclusion eU.inv).functor_isFibered
  letI := (isLocalEmbedding_of_isInclusion eV.hom).functor_isFibered
  letI := Monotone.functor_isFibered_comp (isMap_of_isInclusion eU.inv).monotone hg.monotone
  letI := Monotone.functor_isFibered_comp
    ((isMap_of_isInclusion eU.inv).comp hg).monotone (isMap_of_isInclusion eV.hom).monotone
  Atom.homMk (fun x => eV.hom (g (eU.inv x)))
    (((isMap_of_isInclusion eU.inv).comp hg).comp (isMap_of_isInclusion eV.hom))

@[simp] theorem Atom.conjHom_apply {P Q : OGP.{0}} {U V : Atom} (eU : P ≅ U.ogp)
    (eV : Q ≅ V.ogp) (g : P → Q) (hg : IsMap g) [hg.monotone.functor.IsFibered]
    (x : U.ogp) : Atom.conjHom eU eV g hg x = eV.hom (g (eU.inv x)) :=
  rfl

theorem Atom.conjHom_id {P : OGP.{0}} {U : Atom} (eU : P ≅ U.ogp) :
    haveI := Monotone.functor_isFibered_id (α := P)
    Atom.conjHom eU eU id (IsMap.id P) = 𝟙 U := by
  ext x
  exact ConcreteCategory.congr_hom eU.inv_hom_id x

theorem Atom.conjHom_comp {P Q R : OGP.{0}} {U V W : Atom} (eU : P ≅ U.ogp)
    (eV : Q ≅ V.ogp) (eW : R ≅ W.ogp) {g : P → Q} {g' : Q → R}
    (hg : IsMap g) (hg' : IsMap g') [hg.monotone.functor.IsFibered]
    [hg'.monotone.functor.IsFibered] :
    haveI := Monotone.functor_isFibered_comp hg.monotone hg'.monotone
    Atom.conjHom eU eV g hg ≫ Atom.conjHom eV eW g' hg' =
      Atom.conjHom eU eW (g' ∘ g) (hg.comp hg') := by
  ext x
  exact congrArg (fun y => eW.hom (g' y)) (ConcreteCategory.congr_hom eV.hom_inv_id (g (eU.inv x)))

theorem Atom.isInclusionHom_conjHom {P Q : OGP.{0}} {U V : Atom} (eU : P ≅ U.ogp)
    (eV : Q ≅ V.ogp) {g : P → Q} (hg : IsMap g) [hg.monotone.functor.IsFibered]
    (hinj : Function.Injective g) : IsInclusionHom (Atom.conjHom eU eV g hg) :=
  (IsInclusion.injective (f := eV.hom)).comp (hinj.comp (IsInclusion.injective (f := eU.inv)))

theorem Atom.isCollapseHom_conjHom {P Q : OGP.{0}} {U V : Atom} (eU : P ≅ U.ogp)
    (eV : Q ≅ V.ogp) {g : P → Q} (hg : IsMap g) [hg.monotone.functor.IsFibered]
    (hsurj : Function.Surjective g) : IsCollapseHom (Atom.conjHom eU eV g hg) :=
  (orderIsoOfIso eV).surjective.comp (hsurj.comp (orderIsoOfIso eU.symm).surjective)

theorem Atom.existsUnique_top (U : Atom) : ∃! t : U.ogp, ∀ x, x ≤ t := by
  obtain ⟨t, ht⟩ := U.isAtom.2
  have ht' : ∀ x : U.ogp, x ≤ t := fun x => LowerSet.mem_Iic_iff.1 (ht ▸ LowerSet.mem_top)
  exact ⟨t, ht', fun y hy => le_antisymm (ht' y) (hy t)⟩

def Atom.top (U : Atom) : U.ogp :=
  Fintype.choose (fun t => ∀ x, x ≤ t) U.existsUnique_top

theorem Atom.le_top (U : Atom) (x : U.ogp) : x ≤ U.top :=
  Fintype.choose_spec (fun t => ∀ y, y ≤ t) U.existsUnique_top x

theorem Atom.Iic_top (U : Atom) : LowerSet.Iic U.top = (⊤ : LowerSet U.ogp) :=
  SetLike.ext fun x => iff_of_true (U.le_top x) LowerSet.mem_top

theorem Atom.coe_bdryFull_top (U : Atom) :
    (U.ogp.bdryFull ⊤ : Set U.ogp) = Set.Iio U.top := by
  rw [← U.Iic_top, bdryFull, coe_bdry_Iic_sup]

theorem Atom.mem_bdryFull_top_iff (U : Atom) (x : U.ogp) :
    x ∈ U.ogp.bdryFull ⊤ ↔ x ≠ U.top := by
  rw [← SetLike.mem_coe, U.coe_bdryFull_top, Set.mem_Iio, lt_iff_le_and_ne]
  exact and_iff_right (U.le_top x)

theorem Atom.dimension_eq (U : Atom) : U.dimension = grade ℕ U.top := by
  have h := U.krullDim_eq_dimension.symm
  rw [← LowerSet.krullDim_top, ← U.Iic_top, LowerSet.krullDim_Iic] at h
  exact_mod_cast h

theorem Atom.grade_le_dimension (U : Atom) (x : U.ogp) : grade ℕ x ≤ U.dimension :=
  U.dimension_eq ▸ grade_mono (U.le_top x)

theorem le_apply_top_of_isCollapseHom {U V : Atom} (f : U ⟶ V) (hf : IsCollapseHom f)
    (x : V.ogp) : x ≤ f U.top := by
  obtain ⟨y, rfl⟩ := hf x
  exact (Atom.isMap f).monotone (U.le_top y)

theorem IsCollapseHom.apply_top {U V : Atom} {f : U ⟶ V} (hf : IsCollapseHom f) :
    f U.top = V.top :=
  le_antisymm (V.le_top _) (le_apply_top_of_isCollapseHom f hf V.top)

theorem dimension_le_of_isCollapseHom {U V : Atom} (f : U ⟶ V) (hf : IsCollapseHom f) :
    V.dimension ≤ U.dimension := by
  have htop : f U.top = V.top := hf.apply_top
  rw [U.dimension_eq, V.dimension_eq, ← htop]
  exact (Atom.isMap f).grade_le U.top

theorem grade_eq_of_isInclusionHom {U V : Atom} (f : U ⟶ V) (hf : IsInclusionHom f)
    (x : U.ogp) : grade ℕ (f x) = grade ℕ x :=
  (Atom.isMorphism_of_isInclusionHom f hf).grade_eq x

theorem dimension_le_of_isInclusionHom {U V : Atom} (f : U ⟶ V) (hf : IsInclusionHom f) :
    U.dimension ≤ V.dimension := by
  rw [U.dimension_eq, V.dimension_eq, ← grade_eq_of_isInclusionHom f hf U.top]
  exact grade_mono (V.le_top _)

theorem isIso_of_bijective {U V : Atom} (f : U ⟶ V) (hb : Function.Bijective f) :
    CategoryTheory.IsIso f := by
  let φ : U.ogp ⟶ V.ogp :=
    ConcreteCategory.ofHom ⟨f, Atom.isMorphism_of_isInclusionHom f hb.1⟩
  have : IsIso φ := (isIso_iff_bijective φ).2 hb
  exact inferInstanceAs (IsIso (Atom.isoOfIso (asIso φ)).hom)

theorem isIso_of_isInclusionHom_of_dimension_eq {U V : Atom} (f : U ⟶ V)
    (hf : IsInclusionHom f) (h : U.dimension = V.dimension) : CategoryTheory.IsIso f := by
  refine isIso_of_bijective f ⟨hf, fun z => ?_⟩
  have htop : f U.top = V.top := by
    refine GradeOrder.eq_of_le_of_grade_le (V.le_top _) (Eq.ge ?_)
    rw [grade_eq_of_isInclusionHom f hf, ← U.dimension_eq, h, V.dimension_eq]
  obtain ⟨y, _, hy⟩ := (Atom.isMap f).fibration (htop ▸ V.le_top z)
  exact ⟨y, hy⟩

theorem isIso_of_isInclusionHom_of_apply_top {U V : Atom} (f : U ⟶ V) (hf : IsInclusionHom f)
    (h : f U.top = V.top) : IsIso f :=
  isIso_of_isInclusionHom_of_dimension_eq f hf (by
    rw [U.dimension_eq, V.dimension_eq, ← h, grade_eq_of_isInclusionHom f hf])

theorem isIso_of_isInclusionHom_of_isCollapseHom {U V : Atom} (f : U ⟶ V)
    (hf : IsInclusionHom f) (hc : IsCollapseHom f) : IsIso f :=
  isIso_of_isInclusionHom_of_apply_top f hf hc.apply_top

theorem exists_greatest_fibre_of_isCollapseHom {U V : Atom} (p : U ⟶ V)
    (hp : IsCollapseHom p) (y : V.ogp) :
    ∃ x : U.ogp, p x = y ∧ ∀ z : U.ogp, p z = y → z ≤ x :=
  (Atom.isMap p).monotone.exists_greatest_fibre U.le_top (le_apply_top_of_isCollapseHom p hp y)

abbrev Atom.ofOGP (P : OGP.{0}) [FinEnum P] [DecidableLE P] (hP : IsAtom P) : Atom :=
  Atom.ofIsAtom (FiniteOGP.ofOGP P) ((isAtom_iff_of_iso (FiniteOGP.ofOGPIso P)).1 hP)

instance instCountableAtom : Countable Atom :=
  Function.Injective.countable (f := fun U : Atom => U.toFiniteOGP) fun _ _ => Atom.ext

end Atoms.Shape
