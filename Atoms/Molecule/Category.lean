import Atoms.Molecule.OrientedGradedPoset
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.StrictInitial
import Mathlib.CategoryTheory.MorphismProperty.Concrete
import Mathlib.Order.SuccPred.InitialSeg
import Mathlib.Topology.Maps.Basic

universe u v w

open CategoryTheory Limits Set Topology

namespace Atoms.Molecule.OGP

variable {P : OGP.{u}} {Q : OGP.{v}} {R : OGP.{w}}

structure IsMorphism (f : P → Q) : Prop where
  bijOn_faces : ∀ x α, BijOn f (P.faces α x) (Q.faces α (f x))

namespace IsMorphism

variable {f : P → Q} {g : Q → R}

theorem id (P : OGP.{u}) : IsMorphism (id : P → P) := ⟨fun _ _ => bijOn_id _⟩

theorem comp (hf : IsMorphism f) (hg : IsMorphism g) : IsMorphism (g ∘ f) :=
  ⟨fun x α => (hg.bijOn_faces (f x) α).comp (hf.bijOn_faces x α)⟩

theorem covBy_apply (hf : IsMorphism f) {x y : P} (h : y ⋖ x) : f y ⋖ f x :=
  ((hf.bijOn_faces x (P.orient h)).mapsTo ⟨h, rfl⟩).1

theorem orient_apply (hf : IsMorphism f) {x y : P} (h : y ⋖ x) :
    Q.orient (hf.covBy_apply h) = P.orient h :=
  ((hf.bijOn_faces x (P.orient h)).mapsTo ⟨h, rfl⟩).2

theorem exists_covBy_apply (hf : IsMorphism f) {x : P} {z : Q} (h : z ⋖ f x) :
    ∃ y, y ⋖ x ∧ f y = z := by
  obtain ⟨y, hy, rfl⟩ := (hf.bijOn_faces x (Q.orient h)).surjOn ⟨h, rfl⟩
  exact ⟨y, hy.1, rfl⟩

theorem grade_eq (hf : IsMorphism f) (x : P) : grade ℕ (f x) = grade ℕ x := by
  induction x using WellFoundedLT.induction with
  | _ x ih =>
    by_cases hx : IsMin x
    · have hfx : IsMin (f x) := fun z hz => by
        by_contra hzx
        obtain ⟨w, -, hw⟩ := exists_le_covBy_of_lt (lt_of_le_not_ge hz hzx)
        obtain ⟨y, hy, -⟩ := hf.exists_covBy_apply hw
        exact hy.lt.not_isMin hx
      rw [isMin_iff_eq_bot.1 (hfx.grade ℕ), isMin_iff_eq_bot.1 (hx.grade ℕ)]
    · obtain ⟨z, hz⟩ := not_isMin_iff.1 hx
      obtain ⟨y, -, hy⟩ := exists_le_covBy_of_lt hz
      have h₁ := Nat.covBy_iff_add_one_eq.1 (hy.grade ℕ)
      have h₂ := Nat.covBy_iff_add_one_eq.1 ((hf.covBy_apply hy).grade ℕ)
      rw [ih y hy.lt] at h₂
      omega

theorem monotone (hf : IsMorphism f) : Monotone f := by
  intro x y hxy
  induction y using WellFoundedLT.induction with
  | _ y ih =>
    rcases hxy.eq_or_lt with rfl | hlt
    · exact le_rfl
    · obtain ⟨w, hxw, hw⟩ := exists_le_covBy_of_lt hlt
      exact (ih w hw.lt hxw).trans (hf.covBy_apply hw).le

theorem fibration (hf : IsMorphism f) : Relation.Fibration (· ≤ ·) (· ≤ ·) f := by
  intro x z hz
  induction x using WellFoundedLT.induction generalizing z with
  | _ x ih =>
    rcases hz.eq_or_lt with rfl | hlt
    · exact ⟨x, le_rfl, rfl⟩
    · obtain ⟨w, hzw, hw⟩ := exists_le_covBy_of_lt hlt
      obtain ⟨y, hy, rfl⟩ := hf.exists_covBy_apply hw
      obtain ⟨v, hv, rfl⟩ := ih y hy.lt hzw
      exact ⟨v, hv.trans hy.le, rfl⟩

theorem continuous (hf : IsMorphism f) : Continuous f :=
  IsUpperSet.monotone_iff_continuous.1 hf.monotone

theorem isClosedMap (hf : IsMorphism f) : IsClosedMap f :=
  IsUpperSet.isClosedMap_iff_fibration.2 hf.fibration

theorem le_iff_of_injective (hf : IsMorphism f) (hinj : Function.Injective f) {x y : P} :
    f x ≤ f y ↔ x ≤ y := by
  refine ⟨fun h => ?_, fun h => hf.monotone h⟩
  obtain ⟨z, hz, hzx⟩ := hf.fibration h
  exact hinj hzx ▸ hz

theorem mem_faces_iff_of_injective (hf : IsMorphism f) (hinj : Function.Injective f) {α : Bool}
    {x y : P} : f y ∈ Q.faces α (f x) ↔ y ∈ P.faces α x :=
  ⟨fun h => by
    obtain ⟨z, hz, hzy⟩ := (hf.bijOn_faces x α).surjOn h
    exact hinj hzy ▸ hz,
  fun h => (hf.bijOn_faces x α).mapsTo h⟩

theorem of_initialSeg (e : P ≤i Q)
    (he : ∀ {x y : P} (h : y ⋖ x), Q.orient (e.apply_covBy_apply_iff.2 h) = P.orient h) :
    IsMorphism e where
  bijOn_faces x α := by
    refine ⟨fun y hy => ⟨e.apply_covBy_apply_iff.2 hy.1, (he hy.1).trans hy.2⟩,
      e.injective.injOn, fun z hz => ?_⟩
    obtain ⟨y, rfl⟩ := e.mem_range_of_rel hz.1.lt
    have hy := e.apply_covBy_apply_iff.1 hz.1
    exact ⟨y, ⟨hy, (he hy).symm.trans hz.2⟩, rfl⟩

theorem of_equiv (e : P ≃ Q) (hc : ∀ x y, e y ⋖ e x ↔ y ⋖ x)
    (he : ∀ {x y : P} (h : y ⋖ x), Q.orient ((hc x y).2 h) = P.orient h) : IsMorphism e where
  bijOn_faces x α := by
    refine ⟨fun y hy => ⟨(hc x y).2 hy.1, (he hy.1).trans hy.2⟩, e.injective.injOn,
      fun z hz => ?_⟩
    obtain ⟨y, rfl⟩ := e.surjective z
    have hy := (hc x y).1 hz.1
    exact ⟨y, ⟨hy, (he hy).symm.trans hz.2⟩, rfl⟩

theorem of_forall_exists {f : P → Q}
    (h : ∀ x, ∃ (S : OGP.{w}) (e : S → P) (s : S), IsMorphism e ∧ IsMorphism (f ∘ e) ∧ e s = x) :
    IsMorphism f where
  bijOn_faces x α := by
    obtain ⟨S, e, s, he, hfe, rfl⟩ := h x
    rw [← (he.bijOn_faces s α).image_eq]
    convert (hfe.bijOn_faces s α).injOn.image_of_comp.bijOn_image using 1
    rw [← image_comp]
    exact (hfe.bijOn_faces s α).image_eq.symm

theorem of_comp_of_injective (hg : IsMorphism g) (hinj : Function.Injective g)
    (hgf : IsMorphism (g ∘ f)) : IsMorphism f where
  bijOn_faces x α := by
    refine ⟨fun y hy => (hg.mem_faces_iff_of_injective hinj).1 ((hgf.bijOn_faces x α).mapsTo hy),
      fun y hy y' hy' h => (hgf.bijOn_faces x α).injOn hy hy' (congrArg g h), fun z hz => ?_⟩
    obtain ⟨y, hy, hyz⟩ := (hgf.bijOn_faces x α).surjOn ((hg.bijOn_faces (f x) α).mapsTo hz)
    exact ⟨y, hy, hinj hyz⟩

end IsMorphism

structure Morphism (P : OGP.{u}) (Q : OGP.{v}) where
  toFun : P → Q
  isMorphism : IsMorphism toFun

namespace Morphism

instance : FunLike (Morphism P Q) P Q where
  coe := toFun
  coe_injective f g h := by cases f; cases g; congr

@[ext] theorem ext {f g : Morphism P Q} (h : ∀ x, f x = g x) : f = g := DFunLike.ext _ _ h

def id (P : OGP.{u}) : Morphism P P := ⟨_root_.id, IsMorphism.id P⟩

def comp (g : Morphism Q R) (f : Morphism P Q) : Morphism P R :=
  ⟨g ∘ f, f.isMorphism.comp g.isMorphism⟩

@[simp] theorem id_apply (x : P) : Morphism.id P x = x := rfl

@[simp] theorem comp_apply (g : Morphism Q R) (f : Morphism P Q) (x : P) :
    g.comp f x = g (f x) :=
  rfl

end Morphism

@[ext] structure Hom (P Q : OGP.{u}) where
  private mk ::
  hom' : Morphism P Q

instance : Category OGP.{u} where
  Hom := Hom
  id P := ⟨Morphism.id P⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory OGP.{u} Morphism where
  hom := Hom.hom'
  ofHom := Hom.mk

section Arrows

variable {P Q R : OGP.{u}}

theorem isMorphism (f : P ⟶ Q) : IsMorphism f := (ConcreteCategory.hom f).isMorphism

def map (f : P ⟶ Q) (U : LowerSet P) : LowerSet Q :=
  ⟨f '' U, (isMorphism f).fibration.isLowerSet_image U.lower⟩

@[simp, norm_cast] theorem coe_map (f : P ⟶ Q) (U : LowerSet P) :
    (map f U : Set Q) = f '' U :=
  rfl

theorem map_comp (f : P ⟶ Q) (g : Q ⟶ R) (U : LowerSet P) : map (f ≫ g) U = map g (map f U) :=
  SetLike.coe_injective (by rw [coe_map, coe_map, coe_map, ConcreteCategory.coe_comp, image_comp])

@[simp] theorem mem_map {f : P ⟶ Q} {U : LowerSet P} {y : Q} :
    y ∈ map f U ↔ ∃ x ∈ U, f x = y :=
  Iff.rfl

def comap (f : P ⟶ Q) (V : LowerSet Q) : LowerSet P :=
  ⟨f ⁻¹' V, V.lower.preimage (isMorphism f).monotone⟩

@[simp, norm_cast] theorem coe_comap (f : P ⟶ Q) (V : LowerSet Q) :
    (comap f V : Set P) = f ⁻¹' V :=
  rfl

@[simp] theorem mem_comap {f : P ⟶ Q} {V : LowerSet Q} {x : P} : x ∈ comap f V ↔ f x ∈ V :=
  Iff.rfl

theorem gc_map_comap (f : P ⟶ Q) : GaloisConnection (map f) (comap f) := fun _ _ =>
  image_subset_iff

theorem map_mono (f : P ⟶ Q) : Monotone (map f) := (gc_map_comap f).monotone_l

theorem map_comap (f : P ⟶ Q) (W : LowerSet Q) : map f (comap f W) = W ⊓ map f ⊤ :=
  SetLike.coe_injective (by
    rw [coe_map, coe_comap, LowerSet.coe_inf, coe_map, LowerSet.coe_top, image_univ,
      image_preimage_eq_inter_range])

theorem map_comap_of_le (f : P ⟶ Q) {W : LowerSet Q} (h : W ≤ map f ⊤) :
    map f (comap f W) = W := by
  rw [map_comap, inf_eq_left.2 h]

theorem map_Iic (f : P ⟶ Q) (x : P) : map f (LowerSet.Iic x) = LowerSet.Iic (f x) :=
  SetLike.coe_injective
    ((Relation.fibration_iff_image_Iic (isMorphism f).monotone).1 (isMorphism f).fibration x)

theorem hom_ext_of_map_sup_eq_top {A B : OGP.{u}} {i : A ⟶ P} {j : B ⟶ P}
    (h : map i ⊤ ⊔ map j ⊤ = ⊤) {f g : P ⟶ Q} (hi : i ≫ f = i ≫ g) (hj : j ≫ f = j ≫ g) :
    f = g := by
  ext x
  have hx : x ∈ map i ⊤ ⊔ map j ⊤ := by rw [h]; exact LowerSet.mem_top
  rcases LowerSet.mem_sup_iff.1 hx with ⟨a, -, rfl⟩ | ⟨b, -, rfl⟩
  · exact ConcreteCategory.congr_hom hi a
  · exact ConcreteCategory.congr_hom hj b

def isoMk (e : P ≃o Q)
    (he : ∀ {x y : P} (h : y ⋖ x), Q.orient ((apply_covBy_apply_iff e).2 h) = P.orient h) :
    P ≅ Q where
  hom := ConcreteCategory.ofHom ⟨e, .of_initialSeg e.toInitialSeg he⟩
  inv := ConcreteCategory.ofHom ⟨e.symm, .of_initialSeg e.symm.toInitialSeg fun {x y} h =>
      (he ((apply_covBy_apply_iff e.symm).2 h)).symm.trans
        (Q.orient_congr (e.apply_symm_apply x) (e.apply_symm_apply y) _ h)⟩
  hom_inv_id := by ext x; exact e.symm_apply_apply x
  inv_hom_id := by ext x; exact e.apply_symm_apply x

def orderIsoOfIso (e : P ≅ Q) : P ≃o Q where
  toFun := e.hom
  invFun := e.inv
  left_inv x := congrArg (fun g : P ⟶ P => g x) e.hom_inv_id
  right_inv y := congrArg (fun g : Q ⟶ Q => g y) e.inv_hom_id
  map_rel_iff' {x y} := by
    refine ⟨fun h => ?_, fun h => (isMorphism e.hom).monotone h⟩
    have hinv (z : P) : e.inv (e.hom z) = z :=
      congrArg (fun g : P ⟶ P => g z) e.hom_inv_id
    exact ((hinv x).symm.le.trans ((isMorphism e.inv).monotone h)).trans (hinv y).le

theorem isIso_iff_bijective (f : P ⟶ Q) : IsIso f ↔ Function.Bijective f := by
  refine ⟨fun _ => (orderIsoOfIso (asIso f)).bijective, fun hb => ?_⟩
  have e : f = (isoMk ⟨Equiv.ofBijective _ hb, (isMorphism f).le_iff_of_injective hb.1⟩
      fun h => (isMorphism f).orient_apply h).hom := by
    ext x
    rfl
  rw [e]
  infer_instance

def empty : OGP.{u} where
  carrier := PEmpty
  orient {x} _ := x.elim

instance : IsEmpty (empty : OGP.{u}) := inferInstanceAs (IsEmpty PEmpty)

def isInitialEmpty : IsInitial (empty : OGP.{u}) :=
  IsInitial.ofUniqueHom (fun _ => ConcreteCategory.ofHom ⟨isEmptyElim, ⟨isEmptyElim⟩⟩)
    fun _ _ => by
      ext x
      exact isEmptyElim x

instance : HasInitial OGP.{u} := isInitialEmpty.hasInitial

instance : HasStrictInitialObjects OGP.{u} where
  out {I _} f hI := by
    have he (y : I) : False := isEmptyElim (hI.to empty y)
    exact (isIso_iff_bijective f).2 ⟨fun a _ _ => (he (f a)).elim, fun y => (he y).elim⟩

class IsInclusion (f : P ⟶ Q) : Prop where
  injective : Function.Injective f

namespace IsInclusion

variable (f : P ⟶ Q) [IsInclusion f]

theorem le_iff {x y : P} : f x ≤ f y ↔ x ≤ y :=
  (isMorphism f).le_iff_of_injective injective

theorem covBy_iff {x y : P} : f y ⋖ f x ↔ y ⋖ x :=
  ⟨CovBy.of_image (OrderEmbedding.ofMapLEIff f fun _ _ => le_iff f), (isMorphism f).covBy_apply⟩

theorem mem_faces_iff {α : Bool} {x y : P} : f y ∈ Q.faces α (f x) ↔ y ∈ P.faces α x :=
  (isMorphism f).mem_faces_iff_of_injective injective

theorem isClosedEmbedding : IsClosedEmbedding f :=
  .of_continuous_injective_isClosedMap (isMorphism f).continuous injective
    (isMorphism f).isClosedMap

instance id (P : OGP.{u}) : IsInclusion (𝟙 P) :=
  ⟨by rw [ConcreteCategory.coe_id]; exact Function.injective_id⟩

instance comp (g : Q ⟶ R) [IsInclusion g] : IsInclusion (f ≫ g) :=
  ⟨by rw [ConcreteCategory.coe_comp]; exact (injective (f := g)).comp injective⟩

instance (priority := 100) of_isIso (f : P ⟶ Q) [IsIso f] : IsInclusion f :=
  ⟨(orderIsoOfIso (asIso f)).injective⟩

end IsInclusion

abbrev inclusions : MorphismProperty OGP.{u} := fun _ _ f => IsInclusion f

instance : inclusions.{u}.IsMultiplicative where
  id_mem P := IsInclusion.id P
  comp_mem f g _ _ := IsInclusion.comp f g

theorem inclusions_eq_injective : inclusions.{u} = MorphismProperty.injective OGP.{u} := by
  ext P Q f
  exact ⟨fun h => h.injective, fun h => ⟨h⟩⟩

def incl (U : LowerSet P) : P.restrict U ⟶ P :=
  ConcreteCategory.ofHom ⟨Subtype.val, by
    have hc (x y : P.restrict U) : (y : P) ⋖ x ↔ y ⋖ x :=
      OrdConnected.apply_covBy_apply_iff (OrderEmbedding.subtype (· ∈ U))
        (by simpa using U.lower.ordConnected)
    exact ⟨fun x α => ⟨fun y hy => ⟨(hc x y).2 hy.1, hy.2⟩, Subtype.val_injective.injOn,
      fun z hz => ⟨⟨z, U.lower hz.1.le x.2⟩, ⟨(hc x ⟨z, _⟩).1 hz.1, hz.2⟩, rfl⟩⟩⟩⟩

@[simp] theorem incl_apply (U : LowerSet P) (x : P.restrict U) : incl U x = x.1 := rfl

instance (U : LowerSet P) : IsInclusion (incl U) := ⟨Subtype.val_injective⟩

@[simp] theorem map_incl_top (U : LowerSet P) : map (incl U) ⊤ = U :=
  SetLike.coe_injective (by
    rw [coe_map, LowerSet.coe_top, image_univ]
    exact Subtype.range_coe)

@[simp] theorem map_top_of_isIso (f : P ⟶ Q) [IsIso f] : map f ⊤ = ⊤ :=
  SetLike.coe_injective (by
    rw [coe_map, LowerSet.coe_top, image_univ]
    exact range_eq_univ.2 (orderIsoOfIso (asIso f)).surjective)

end Arrows

def IsLocalEmbedding (f : P → Q) : Prop :=
  ∀ x : P, IsClosedEmbedding ((closure {x} : Set P).domRestrict f)

theorem IsLocalEmbedding.isClosedMap {f : P → Q} (hf : IsLocalEmbedding f) : IsClosedMap f := by
  refine IsUpperSet.isClosedMap_iff_fibration.2
    (Relation.fibration_iff_isLowerSet_image_Iic.2 fun x => ?_)
  have h := (hf x).isClosedMap _ isClosed_univ
  rwa [image_univ, range_domRestrict, IsUpperSet.closure_singleton,
    IsUpperSet.isClosed_iff_isLower] at h

end Atoms.Molecule.OGP
