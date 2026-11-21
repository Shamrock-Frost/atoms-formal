import Atoms.Diagrammatic.Pasting.Basic
import Atoms.Diagrammatic.RealizationColimits

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Order Atoms.Shape

universe u

namespace Atoms.Diagrammatic

theorem hom_ext_realize_of_isEmpty {C : RDCpx.{0}} (hC : IsEmpty C.obj.toOGP)
    {Z : DiagSet.{u}} (m m' : realize.obj C ⟶ Z) : m = m' := by
  ext T f
  exact isEmptyElim (ConcreteCategory.hom (show atomToRDCpx.obj T.unop ⟶ C from f.down).hom
    T.unop.top)

section Cover

variable {R U V : RDCpx.{0}} (i : U.obj.toOGP ⟶ R.obj.toOGP) (j : V.obj.toOGP ⟶ R.obj.toOGP)
  [IsInclusion i] [IsInclusion j]

noncomputable def restrictIso : U ≅ R.restrict (map i ⊤) :=
  haveI := isIso_codRestrict i (C := map i ⊤) rfl
  RDCpx.isoOfIso (asIso (codRestrict i (map i ⊤) fun x => ⟨x, LowerSet.mem_top, rfl⟩))

noncomputable abbrev restrictInv : R.restrict (map i ⊤) ⟶ U :=
  (restrictIso i).inv

private theorem restrictIso_hom_comp_restrictIncl :
    (restrictIso i).hom ≫ R.restrictIncl (map i ⊤) = RDCpx.ofInclusion i := by
  ext x
  rfl

private theorem restrictInv_comp_ofInclusion :
    restrictInv i ≫ RDCpx.ofInclusion i = R.restrictIncl (map i ⊤) := by
  rw [← restrictIso_hom_comp_restrictIncl i, Iso.inv_hom_id_assoc]

private theorem apply_restrictInv (y : (R.restrict (map i ⊤)).obj) :
    i (ConcreteCategory.hom (restrictInv i).hom y) = y.1 := by
  have := isIso_codRestrict i (C := map i ⊤) rfl
  let e : U.obj.toOGP ≅ R.obj.toOGP.restrict (map i ⊤) :=
    asIso (codRestrict i (map i ⊤) fun x => ⟨x, LowerSet.mem_top, rfl⟩)
  exact congrArg Subtype.val (e.inv_hom_id_apply y)

omit [IsInclusion i] [IsInclusion j] in
theorem isPushout_realize_cover (hcov : map i ⊤ ⊔ map j ⊤ = ⊤) :
    IsPushout
      (realize.{u}.map (RDCpx.inclusion R (inf_le_left : map i ⊤ ⊓ map j ⊤ ≤ map i ⊤)))
      (realize.map (RDCpx.inclusion R (inf_le_right : map i ⊤ ⊓ map j ⊤ ≤ map j ⊤)))
      (realize.map (RDCpx.restrictIncl R (map i ⊤)))
      (realize.map (RDCpx.restrictIncl R (map j ⊤))) :=
  isPushout_realize_of_union R hcov

def CoverCompatible {Z : DiagSet.{u}} (a : realize.obj U ⟶ Z) (b : realize.obj V ⟶ Z) : Prop :=
  realize.map (RDCpx.inclusion R (inf_le_left : map i ⊤ ⊓ map j ⊤ ≤ map i ⊤)) ≫
      realize.map (restrictInv i) ≫ a =
    realize.map (RDCpx.inclusion R (inf_le_right : map i ⊤ ⊓ map j ⊤ ≤ map j ⊤)) ≫
      realize.map (restrictInv j) ≫ b

noncomputable def coverDesc (hcov : map i ⊤ ⊔ map j ⊤ = ⊤)
    {Z : DiagSet.{u}} (a : realize.obj U ⟶ Z) (b : realize.obj V ⟶ Z)
    (hab : CoverCompatible i j a b) : realize.obj R ⟶ Z :=
  (isPushout_realize_cover i j hcov).desc (realize.map (restrictInv i) ≫ a)
    (realize.map (restrictInv j) ≫ b) hab

private theorem ofInclusion_comp_of_restrictIncl {Z : DiagSet.{u}} {g : realize.obj R ⟶ Z}
    {a : realize.obj U ⟶ Z}
    (h : realize.map (RDCpx.restrictIncl R (map i ⊤)) ≫ g =
      realize.map (restrictInv i) ≫ a) :
    realize.map (RDCpx.ofInclusion i) ≫ g = a := by
  calc realize.map (RDCpx.ofInclusion i) ≫ g
      = realize.map (restrictIso i).hom ≫
          realize.map (RDCpx.restrictIncl R (map i ⊤)) ≫ g :=
        (congrArg (fun t => realize.map t ≫ g)
          (restrictIso_hom_comp_restrictIncl i).symm).trans (realize.map_comp_assoc _ _ _)
    _ = realize.map (restrictIso i).hom ≫ realize.map (restrictInv i) ≫ a :=
        congrArg (realize.map (restrictIso i).hom ≫ ·) h
    _ = realize.map ((restrictIso i).hom ≫ restrictInv i) ≫ a :=
        (realize.map_comp_assoc _ _ _).symm
    _ = a :=
        (congrArg (fun t => realize.map t ≫ a) (restrictIso i).hom_inv_id).trans
          ((congrArg (· ≫ a) (realize.map_id _)).trans (Category.id_comp a))

theorem ofInclusion_coverDesc_left (hcov : map i ⊤ ⊔ map j ⊤ = ⊤) {Z : DiagSet.{u}}
    (a : realize.obj U ⟶ Z) (b : realize.obj V ⟶ Z) (hab : CoverCompatible i j a b) :
    realize.map (RDCpx.ofInclusion i) ≫ coverDesc i j hcov a b hab = a :=
  ofInclusion_comp_of_restrictIncl i ((isPushout_realize_cover i j hcov).inl_desc _ _ hab)

theorem ofInclusion_coverDesc_right (hcov : map i ⊤ ⊔ map j ⊤ = ⊤) {Z : DiagSet.{u}}
    (a : realize.obj U ⟶ Z) (b : realize.obj V ⟶ Z) (hab : CoverCompatible i j a b) :
    realize.map (RDCpx.ofInclusion j) ≫ coverDesc i j hcov a b hab = b :=
  ofInclusion_comp_of_restrictIncl j ((isPushout_realize_cover i j hcov).inr_desc _ _ hab)

theorem hom_ext_cover (hcov : map i ⊤ ⊔ map j ⊤ = ⊤)
    {Z : DiagSet.{u}} {m m' : realize.obj R ⟶ Z}
    (h₁ : realize.map (RDCpx.ofInclusion i) ≫ m = realize.map (RDCpx.ofInclusion i) ≫ m')
    (h₂ : realize.map (RDCpx.ofInclusion j) ≫ m = realize.map (RDCpx.ofInclusion j) ≫ m') :
    m = m' := by
  refine (isPushout_realize_cover i j hcov).hom_ext ?_ ?_
  · rw [← restrictInv_comp_ofInclusion, realize.map_comp_assoc, realize.map_comp_assoc, h₁]
  · rw [← restrictInv_comp_ofInclusion, realize.map_comp_assoc, realize.map_comp_assoc, h₂]

theorem coverCompatible_of_emb {Z : DiagSet.{u}} (a : realize.obj U ⟶ Z) (b : realize.obj V ⟶ Z)
    {C : RDCpx.{0}} (c : C.obj.toOGP ⟶ U.obj.toOGP) (d : C.obj.toOGP ⟶ V.obj.toOGP)
    [IsInclusion c] [IsInclusion d]
    (hcd : ∀ y, i (c y) = j (d y))
    (himg : map (c ≫ i) ⊤ = map i ⊤ ⊓ map j ⊤)
    (hab : realize.map (RDCpx.ofInclusion c) ≫ a = realize.map (RDCpx.ofInclusion d) ≫ b) :
    CoverCompatible i j a b := by
  have := isIso_codRestrict (c ≫ i) himg
  let e : C.obj.toOGP ≅ R.obj.toOGP.restrict (map i ⊤ ⊓ map j ⊤) :=
    asIso (codRestrict (c ≫ i) _ fun x => himg ▸ ⟨x, LowerSet.mem_top, rfl⟩)
  let g : R.restrict (map i ⊤ ⊓ map j ⊤) ⟶ C :=
    (RDCpx.isoOfIso (P := R.restrict (map i ⊤ ⊓ map j ⊤)) (Q := C) e.symm).hom
  have hg : ∀ x : (R.restrict (map i ⊤ ⊓ map j ⊤)).obj,
      i (c (ConcreteCategory.hom g.hom x)) = x.1 := fun x =>
    congrArg Subtype.val (e.inv_hom_id_apply x)
  have h₁ : RDCpx.inclusion R (inf_le_left : map i ⊤ ⊓ map j ⊤ ≤ map i ⊤) ≫ restrictInv i =
      g ≫ RDCpx.ofInclusion c := by
    ext x
    exact IsInclusion.injective (f := i) ((apply_restrictInv i _).trans (hg x).symm)
  have h₂ : RDCpx.inclusion R (inf_le_right : map i ⊤ ⊓ map j ⊤ ≤ map j ⊤) ≫ restrictInv j =
      g ≫ RDCpx.ofInclusion d := by
    ext x
    exact IsInclusion.injective (f := j)
      ((apply_restrictInv j _).trans ((hg x).symm.trans (hcd _)))
  rw [CoverCompatible, ← realize.map_comp_assoc, h₁, realize.map_comp_assoc, hab,
    ← realize.map_comp_assoc, ← h₂, realize.map_comp_assoc]

end Cover

end Atoms.Diagrammatic

namespace Atoms.Diagrammatic.PastingDiagram

variable {X Y : DiagSet.{u}}

section Degenerate

structure DegeneracyFactorization (u : PastingDiagram X) where
  target : RDCpx.{0}
  proj : u.shape.rdc ⟶ target
  map : realize.obj target ⟶ X
  surjective : Function.Surjective (ConcreteCategory.hom proj.hom)
  dim_lt : krullDim target.obj.toOGP < u.dim
  comp_eq : realize.map proj ≫ map = u.map

def IsDegenerate (u : PastingDiagram X) : Prop :=
  Nonempty (DegeneracyFactorization u)

noncomputable def IsDegenerate.factorization {u : PastingDiagram X} (h : u.IsDegenerate) :
    DegeneracyFactorization u :=
  h.some

theorem isDegenerate_ofCell_iff {U : Atom} (x : diagram X U) :
    (ofCell x).IsDegenerate ↔ Atoms.Diagrammatic.IsDegenerate X x := by
  constructor
  · rintro ⟨⟨Q, p, v, hs, hd, hm⟩⟩
    classical
    have : FinEnum Q.obj.toOGP :=
      FinEnum.ofSurjective (β := U.ogp) (ConcreteCategory.hom p.hom) hs
    let p₀ : atomToRDCpx.obj U ⟶ Q := p
    let t := ConcreteCategory.hom p₀.hom U.top
    have hmem : ∀ z, ConcreteCategory.hom p₀.hom z ∈ LowerSet.Iic t :=
      hom_apply_mem_closure_apply_top p₀
    let q : U ⟶ principalAtomRDC Q t := principalLiftRDC Q t p₀ hmem
    have hq : atomToRDCpx.map q ≫ principalInclusionRDC Q t = p₀ :=
      principalLiftRDC_comp_principalInclusionRDC Q t p₀ hmem
    have hsq : IsCollapseHom q := fun w => by
      obtain ⟨z, hz⟩ := hs (ConcreteCategory.hom (principalInclusionRDC Q t).hom w)
      exact ⟨z, injective_principalInclusionRDC Q t
        ((congrArg (fun f : atomToRDCpx.obj U ⟶ Q => ConcreteCategory.hom f.hom z) hq).trans hz)⟩
    refine ⟨principalAtomRDC Q t, q, v.app (op _) ⟨principalInclusionRDC Q t⟩, hsq, ?_, ?_⟩
    · intro hiso
      have hinv : IsCollapseHom (CategoryTheory.inv q) := fun z =>
        ⟨q z, ConcreteCategory.congr_hom (CategoryTheory.IsIso.hom_inv_id q) z⟩
      have h₁ : U.dimension ≤ grade ℕ t :=
        (dimension_le_of_isCollapseHom (CategoryTheory.inv q) hinv).trans_eq
          (dimension_principalAtomRDC Q t)
      have h₂ : ((U.dimension : ℕ) : WithBot ℕ∞) ≤ krullDim Q.obj.toOGP :=
        (Nat.cast_le.2 h₁).trans (grade_le_krullDim t)
      exact absurd h₂ (not_le.2 hd)
    · have hx : v.app (op U) ⟨p₀⟩ = x :=
        (congrArg (fun m => m.app (op U) ⟨𝟙 (atomToRDCpx.obj U)⟩) hm).trans
          (X.map_id_apply (op U) x)
      exact (NatTrans.naturality_apply v q.op ⟨principalInclusionRDC Q t⟩).symm.trans
        ((congrArg (v.app (op U)) (congrArg ULift.up hq)).trans hx)
  · rintro ⟨V, p, y, hp, hni, hy⟩
    refine ⟨⟨atomToRDCpx.obj V, atomToRDCpx.map p,
      (realizeAtomIso V).hom ≫ uliftYonedaEquiv.symm y, hp, ?_, ?_⟩⟩
    · have hlt : V.dimension < U.dimension :=
        lt_of_le_of_ne (dimension_le_of_isCollapseHom p hp) fun h =>
          hni (isIso_of_isCollapseHom_of_dimension_eq p hp h.symm)
      rw [show krullDim (atomToRDCpx.obj V).obj.toOGP = V.dimension from V.krullDim_eq_dimension]
      exact_mod_cast hlt
    · have e₁ : realize.map (atomToRDCpx.map p) ≫ (realizeAtomIso V).hom =
          (realizeAtomIso U).hom ≫ uliftYoneda.{u}.map p := by
        ext ⟨T⟩ g
        rfl
      change realize.map (atomToRDCpx.map p) ≫ (realizeAtomIso V).hom ≫ uliftYonedaEquiv.symm y =
        (realizeAtomIso U).hom ≫ uliftYonedaEquiv.symm x
      calc realize.map (atomToRDCpx.map p) ≫ (realizeAtomIso V).hom ≫ uliftYonedaEquiv.symm y
          = (realize.map (atomToRDCpx.map p) ≫ (realizeAtomIso V).hom) ≫
              uliftYonedaEquiv.symm y := (Category.assoc _ _ _).symm
        _ = ((realizeAtomIso U).hom ≫ uliftYoneda.{u}.map p) ≫ uliftYonedaEquiv.symm y :=
            congrArg (· ≫ uliftYonedaEquiv.symm y) e₁
        _ = (realizeAtomIso U).hom ≫ uliftYonedaEquiv.symm (X.map p.op y) :=
            (Category.assoc _ _ _).trans (congrArg ((realizeAtomIso U).hom ≫ ·)
              ((uliftYonedaEquiv_symm_map p.op y).symm))
        _ = (realizeAtomIso U).hom ≫ uliftYonedaEquiv.symm x :=
            congrArg (fun z => (realizeAtomIso U).hom ≫ uliftYonedaEquiv.symm z) hy

theorem IsDegenerate.mapTo {u : PastingDiagram X} (h : u.IsDegenerate) (f : X ⟶ Y) :
    (u.mapTo f).IsDegenerate := by
  obtain ⟨⟨Q, p, v, hs, hd, hm⟩⟩ := h
  exact ⟨⟨Q, p, v ≫ f, hs, hd, (Category.assoc _ _ _).symm.trans (congrArg (· ≫ f) hm)⟩⟩

end Degenerate

theorem boundary_mapTo (u : PastingDiagram X) (f : X ⟶ Y) (k : ℕ) (α : Bool) :
    (u.mapTo f).boundary k α = (u.boundary k α).mapTo f :=
  congrArg (PastingDiagram.mk (u.shape.boundary k α)) (Category.assoc _ _ _).symm

theorem boundary_ofCell_taut_mapTo {V : Atom} (c : diagram X V) (k : ℕ) (α : Bool) :
    ((ofCell (uliftYonedaEquiv (𝟙 (ball.{u} V)))).boundary k α).mapTo (uliftYonedaEquiv.symm c) =
      (ofCell c).boundary k α := by
  rw [← boundary_mapTo, ← ofCell_app]
  exact congrArg (fun d : diagram X V => (ofCell d).boundary k α)
    (Equiv.apply_symm_apply uliftYonedaEquiv c)

theorem Equiv.mapTo {u v : PastingDiagram X} (h : u.Equiv v) (f : X ⟶ Y) :
    (u.mapTo f).Equiv (v.mapTo f) := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨φ, (Category.assoc _ _ _).symm.trans (congrArg (· ≫ f) hφ)⟩

theorem Equiv.mapTo_boundary {u b : PastingDiagram X} {k : ℕ} {α : Bool}
    (h : (u.boundary k α).Equiv b) (f : X ⟶ Y) : ((u.mapTo f).boundary k α).Equiv (b.mapTo f) := by
  rw [boundary_mapTo]
  exact h.mapTo f

theorem Equiv.boundary_mapTo {u v : PastingDiagram X} {k m : ℕ} {α β : Bool}
    (h : (u.boundary k α).Equiv (v.boundary m β)) (f : X ⟶ Y) :
    ((u.mapTo f).boundary k α).Equiv ((v.mapTo f).boundary m β) := by
  rw [PastingDiagram.boundary_mapTo, PastingDiagram.boundary_mapTo]
  exact h.mapTo f

theorem Equiv.of_mapTo {u v : PastingDiagram X} (f : X ⟶ Y) [Mono f]
    (h : (u.mapTo f).Equiv (v.mapTo f)) : u.Equiv v := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨φ, (cancel_mono f).1 (by rw [Category.assoc]; exact hφ)⟩

section Ambient

theorem equiv_of_emb_of_image_eq {a b : PastingDiagram X} {C : RDCpx.{0}}
    (w : realize.obj C ⟶ X) (f : a.shape.ogp ⟶ C.obj.toOGP)
    (g : b.shape.ogp ⟶ C.obj.toOGP) [IsInclusion f] [IsInclusion g]
    (hf : realize.map (RDCpx.ofInclusion (P := a.shape.rdc) (Q := C) f) ≫ w = a.map)
    (hg : realize.map (RDCpx.ofInclusion (P := b.shape.rdc) (Q := C) g) ≫ w = b.map)
    (h : OGP.map f ⊤ = OGP.map g ⊤) : a.Equiv b := by
  obtain ⟨ef, hef⟩ := exists_iso_restrict f h
  obtain ⟨eg, heg⟩ := exists_iso_restrict g rfl
  refine ⟨ef ≪≫ eg.symm, ?_⟩
  have E : (RDCpx.isoOfIso (P := a.shape.rdc) (Q := b.shape.rdc) (ef ≪≫ eg.symm)).hom ≫
      RDCpx.ofInclusion (P := b.shape.rdc) (Q := C) g =
        RDCpx.ofInclusion (P := a.shape.rdc) (Q := C) f := by
    ext x
    have h1 : g (eg.inv (ef.hom x)) = (incl (OGP.map g ⊤) (eg.hom (eg.inv (ef.hom x)))) :=
      (ConcreteCategory.congr_hom heg (eg.inv (ef.hom x))).symm
    have h2 : incl (OGP.map g ⊤) (eg.hom (eg.inv (ef.hom x))) = incl (OGP.map g ⊤) (ef.hom x) :=
      congrArg (incl (OGP.map g ⊤)) (eg.inv_hom_id_apply (ef.hom x))
    have h3 : incl (OGP.map g ⊤) (ef.hom x) = f x :=
      ConcreteCategory.congr_hom hef x
    exact h1.trans (h2.trans h3)
  rw [← hg, ← hf, ← Category.assoc, ← realize.map_comp]
  exact congrArg (fun t => realize.map t ≫ w) E

private theorem equiv_of_emb_of_image_eq_shape {a b c : PastingDiagram X}
    (f : a.shape.ogp ⟶ c.shape.ogp) (g : b.shape.ogp ⟶ c.shape.ogp)
    [IsInclusion f] [IsInclusion g]
    (hf : realize.map (RDCpx.ofInclusion (P := a.shape.rdc) (Q := c.shape.rdc) f) ≫ c.map = a.map)
    (hg : realize.map (RDCpx.ofInclusion (P := b.shape.rdc) (Q := c.shape.rdc) g) ≫ c.map = b.map)
    (h : OGP.map f ⊤ = OGP.map g ⊤) : a.Equiv b :=
  equiv_of_emb_of_image_eq c.map f g hf hg h

private theorem ofInclusion_comp_isoOfIso_map {a b : PastingDiagram X} {C P : RDCpx.{0}}
    (m : realize.obj C ⟶ X) (eb : a.shape.ogp ⟶ C.obj.toOGP) [IsInclusion eb]
    (heb : realize.map (RDCpx.ofInclusion (P := a.shape.rdc) (Q := C) eb) ≫ m = a.map)
    {i : P.obj.toOGP ⟶ C.obj.toOGP} {i' : P.obj.toOGP ⟶ b.shape.ogp}
    {i₀ : P.obj.toOGP ⟶ a.shape.ogp} [IsInclusion i] [IsInclusion i'] [IsInclusion i₀]
    (Θ : a.shape.ogp ≅ b.shape.ogp)
    (hi : realize.map (RDCpx.ofInclusion i) ≫ m =
      realize.map (RDCpx.ofInclusion (P := P) (Q := b.shape.rdc) i') ≫ b.map)
    (hi₀ : i₀ ≫ eb = i) (hΘ : i₀ ≫ Θ.hom = i') :
    realize.map (RDCpx.ofInclusion (P := P) (Q := a.shape.rdc) i₀) ≫
        realize.map (RDCpx.isoOfIso (P := a.shape.rdc) (Q := b.shape.rdc) Θ).hom ≫ b.map =
      realize.map (RDCpx.ofInclusion (P := P) (Q := a.shape.rdc) i₀) ≫ a.map := by
  have E : RDCpx.ofInclusion (P := P) (Q := a.shape.rdc) i₀ ≫
      (RDCpx.isoOfIso (P := a.shape.rdc) (Q := b.shape.rdc) Θ).hom =
      RDCpx.ofInclusion (P := P) (Q := b.shape.rdc) i' := by
    ext x
    exact ConcreteCategory.congr_hom hΘ x
  have F : RDCpx.ofInclusion (P := P) (Q := a.shape.rdc) i₀ ≫
      RDCpx.ofInclusion (P := a.shape.rdc) (Q := C) eb = RDCpx.ofInclusion i := by
    ext x
    exact ConcreteCategory.congr_hom hi₀ x
  rw [← realize.map_comp_assoc, E, ← hi, ← F, realize.map_comp_assoc, heb]

theorem exists_iso_of_covers {a b : PastingDiagram X} {C P Q : RDCpx.{0}}
    (m : realize.obj C ⟶ X) (eb : a.shape.ogp ⟶ C.obj.toOGP) [IsInclusion eb]
    (heb : realize.map (RDCpx.ofInclusion (P := a.shape.rdc) (Q := C) eb) ≫ m = a.map)
    (i : P.obj.toOGP ⟶ C.obj.toOGP) (j : Q.obj.toOGP ⟶ C.obj.toOGP)
    [IsInclusion i] [IsInclusion j]
    (hij : OGP.map i ⊤ ⊔ OGP.map j ⊤ = OGP.map eb ⊤)
    (i' : P.obj.toOGP ⟶ b.shape.ogp) (j' : Q.obj.toOGP ⟶ b.shape.ogp)
    [IsInclusion i'] [IsInclusion j']
    (hij' : OGP.map i' ⊤ ⊔ OGP.map j' ⊤ = ⊤)
    (hc : ∀ x y, i x = j y ↔ i' x = j' y)
    (hi : realize.map (RDCpx.ofInclusion i) ≫ m =
      realize.map (RDCpx.ofInclusion (P := P) (Q := b.shape.rdc) i') ≫ b.map)
    (hj : realize.map (RDCpx.ofInclusion j) ≫ m =
      realize.map (RDCpx.ofInclusion (P := Q) (Q := b.shape.rdc) j') ≫ b.map) :
    ∃ Θ : a.shape.ogp ≅ b.shape.ogp,
      realize.map (RDCpx.isoOfIso (P := a.shape.rdc) (Q := b.shape.rdc) Θ).hom ≫ b.map = a.map ∧
      (∀ x, eb (Θ.inv (i' x)) = i x) ∧ (∀ y, eb (Θ.inv (j' y)) = j y) := by
  obtain ⟨e, he⟩ := exists_iso_restrict eb rfl
  have he' : e.inv ≫ eb = incl (OGP.map eb ⊤) := (Iso.inv_comp_eq e).2 he.symm
  have memi : ∀ x, i x ∈ OGP.map eb ⊤ := fun x =>
    hij ▸ LowerSet.mem_sup_iff.2 (Or.inl ⟨x, LowerSet.mem_top, rfl⟩)
  have memj : ∀ y, j y ∈ OGP.map eb ⊤ := fun y =>
    hij ▸ LowerSet.mem_sup_iff.2 (Or.inr ⟨y, LowerSet.mem_top, rfl⟩)
  let i₀ : P.obj.toOGP ⟶ a.shape.ogp := codRestrict i (OGP.map eb ⊤) memi ≫ e.inv
  let j₀ : Q.obj.toOGP ⟶ a.shape.ogp := codRestrict j (OGP.map eb ⊤) memj ≫ e.inv
  have hi₀_hom : i₀ ≫ eb = i := by
    rw [Category.assoc, he', codRestrict_incl]
  have hj₀_hom : j₀ ≫ eb = j := by
    rw [Category.assoc, he', codRestrict_incl]
  have hi₀ (x : P.obj.toOGP) : eb (i₀ x) = i x := ConcreteCategory.congr_hom hi₀_hom x
  have hj₀ (y : Q.obj.toOGP) : eb (j₀ y) = j y := ConcreteCategory.congr_hom hj₀_hom y
  have hcov₀ : OGP.map i₀ ⊤ ⊔ OGP.map j₀ ⊤ = ⊤ := by
    refine map_injective eb ?_
    rw [OGP.map_sup, ← map_comp, ← map_comp, hi₀_hom, hj₀_hom, hij]
  have hc₀ (x : P.obj.toOGP) (y : Q.obj.toOGP) : i₀ x = j₀ y ↔ i' x = j' y := by
    rw [← (IsInclusion.injective (f := eb)).eq_iff, hi₀, hj₀, hc]
  obtain ⟨Θ, hΘi, hΘj, hΘi', hΘj'⟩ := exists_iso_of_cover_pair i₀ j₀ i' j' hcov₀ hij' hc₀
  refine ⟨Θ, hom_ext_cover (U := P) (V := Q) (R := a.shape.rdc) i₀ j₀ hcov₀
    (ofInclusion_comp_isoOfIso_map m eb heb Θ hi hi₀_hom hΘi)
    (ofInclusion_comp_isoOfIso_map m eb heb Θ hj hj₀_hom hΘj), fun x => ?_, fun y => ?_⟩
  · exact (congrArg eb (ConcreteCategory.congr_hom hΘi' x)).trans (hi₀ x)
  · exact (congrArg eb (ConcreteCategory.congr_hom hΘj' y)).trans (hj₀ y)

end Ambient

section Pasting

theorem equiv_boundary_of_emb (a b : PastingDiagram X)
    (f : a.shape.ogp ⟶ b.shape.ogp) [IsInclusion f]
    (hf : realize.map (RDCpx.ofInclusion (P := a.shape.rdc) (Q := b.shape.rdc) f) ≫ b.map = a.map)
    {k m : ℕ} {α β : Bool}
    (h : OGP.map f (a.shape.ogp.boundary ⊤ k α) = b.shape.ogp.boundary ⊤ m β) :
    (b.boundary m β).Equiv (a.boundary k α) := by
  let g : (a.shape.boundary k α).ogp ⟶ b.shape.ogp := a.shape.boundaryIncl k α ≫ f
  refine equiv_of_emb_of_image_eq_shape (c := b) (b.shape.boundaryIncl m β) g rfl ?_ ?_
  · have hcomp : RDCpx.ofInclusion (P := (a.shape.boundary k α).rdc) (Q := b.shape.rdc) g =
        a.shape.boundaryInclRDC k α ≫
          RDCpx.ofInclusion (P := a.shape.rdc) (Q := b.shape.rdc) f := by
      ext x
      rfl
    rw [hcomp, realize.map_comp_assoc, hf, boundary_map]
  · rw [b.shape.map_boundaryIncl_top, ← h, show g = a.shape.boundaryIncl k α ≫ f from rfl,
      map_comp, a.shape.map_boundaryIncl_top]

theorem Equiv.boundary {u v : PastingDiagram X} (h : u.Equiv v) (k : ℕ) (α : Bool) :
    (u.boundary k α).Equiv (v.boundary k α) := by
  obtain ⟨φ, hφ⟩ := h
  refine (equiv_boundary_of_emb u v φ.hom hφ ?_).symm
  rw [map_boundary, map_top_of_isIso]

theorem equiv_boundary_boundary (u : PastingDiagram X) {j k : ℕ} (hj : j < k) (α β : Bool) :
    ((u.boundary k α).boundary j β).Equiv (u.boundary j β) := by
  let g : ((u.shape.boundary k α).boundary j β).ogp ⟶ u.shape.ogp :=
    (u.shape.boundary k α).boundaryIncl j β ≫ u.shape.boundaryIncl k α
  refine equiv_of_emb_of_image_eq_shape (c := u) g (u.shape.boundaryIncl j β) ?_ rfl ?_
  · have hcomp :
        RDCpx.ofInclusion (P := ((u.shape.boundary k α).boundary j β).rdc) (Q := u.shape.rdc) g =
        (u.shape.boundary k α).boundaryInclRDC j β ≫ u.shape.boundaryInclRDC k α := by
      ext x
      rfl
    rw [hcomp, realize.map_comp_assoc]
    rfl
  · rw [show g = (u.shape.boundary k α).boundaryIncl j β ≫ u.shape.boundaryIncl k α from rfl,
      map_comp, (u.shape.boundary k α).map_boundaryIncl_top, map_boundary,
      u.shape.map_boundaryIncl_top, u.shape.map_boundaryIncl_top,
      u.shape.isMolecule.isGlobular j k hj β α]

theorem equiv_boundary_dim (u : PastingDiagram X) {k : ℕ} (hk : u.dim ≤ k) (α : Bool) :
    (u.boundary k α).Equiv u := by
  refine equiv_of_emb_of_image_eq_shape (c := u) (u.shape.boundaryIncl k α) (𝟙 u.shape.ogp)
    rfl ?_ ?_
  · simp only [MoleculeShape.ofInclusion_id, realize.map_id, Category.id_comp]
  · rw [u.shape.map_boundaryIncl_top, map_top_of_isIso, boundary_eq_self _ α]
    rw [LowerSet.krullDim_top, u.shape.krullDim_eq_dimension]
    exact_mod_cast hk

theorem le_dim_of_dim_boundary (d : PastingDiagram X) {k : ℕ} {α : Bool}
    (h : (d.boundary k α).dim = k) : k ≤ d.dim := by
  by_contra hlt
  have e := dim_eq_of_equiv (equiv_boundary_dim d (by omega : d.dim ≤ k) α)
  omega

variable (u v : PastingDiagram X) (k : ℕ)
  (ψ : (u.boundary k true).shape.ogp ≅ (v.boundary k false).shape.ogp)

def pasteInl : u.shape.ogp ⟶ (u.shape.paste v.shape k ψ).ogp :=
  glue.inl (u.shape.gluingIso v.shape k ψ) ≫ (u.shape.pasteIso v.shape k ψ).hom

instance : IsInclusion (pasteInl u v k ψ) :=
  inferInstanceAs (IsInclusion (glue.inl _ ≫ (u.shape.pasteIso v.shape k ψ).hom))

def pasteInr : v.shape.ogp ⟶ (u.shape.paste v.shape k ψ).ogp :=
  glue.inr (u.shape.gluingIso v.shape k ψ) ≫ (u.shape.pasteIso v.shape k ψ).hom

instance : IsInclusion (pasteInr u v k ψ) :=
  inferInstanceAs (IsInclusion (glue.inr _ ≫ (u.shape.pasteIso v.shape k ψ).hom))

theorem isPastingIn_paste :
    (u.shape.paste v.shape k ψ).ogp.IsPastingIn k (OGP.map (pasteInl u v k ψ) ⊤)
      (OGP.map (pasteInr u v k ψ) ⊤) ⊤ := by
  have h := (isPastingIn_map_iff (u.shape.pasteIso v.shape k ψ).hom k _ _ ⊤).2
    (isPastingIn_glue u.shape.ogp v.shape.ogp k (u.shape.gluingIso v.shape k ψ))
  rw [pasteInl, pasteInr]
  rwa [map_top_of_isIso (u.shape.pasteIso v.shape k ψ).hom, ← map_comp, ← map_comp] at h

theorem coverCompatible_paste
    (hab : realize.map (RDCpx.isoOfIso (P := (u.boundary k true).shape.rdc)
      (Q := (v.boundary k false).shape.rdc) ψ).hom ≫ (v.boundary k false).map =
        (u.boundary k true).map) :
    CoverCompatible (U := u.shape.rdc) (V := v.shape.rdc) (R := (u.shape.paste v.shape k ψ).rdc)
      (pasteInl u v k ψ) (pasteInr u v k ψ) u.map v.map := by
  have hp := isPastingIn_paste u v k ψ
  let d : (u.shape.boundary k true).ogp ⟶ v.shape.ogp := ψ.hom ≫ v.shape.boundaryIncl k false
  have hcond : u.shape.boundaryIncl k true ≫ pasteInl u v k ψ =
      d ≫ pasteInr u v k ψ := by
    dsimp [d, MoleculeShape.boundary, MoleculeShape.boundaryIncl, MoleculeShape.subIncl,
      pasteInl, pasteInr, MoleculeShape.gluingIso]
    rw [Category.assoc, Category.assoc, ← Category.assoc (incl _), glue.condition]
    simp only [Category.assoc, Iso.trans_hom, Iso.inv_hom_id_assoc]
    rfl
  refine coverCompatible_of_emb (U := u.shape.rdc) (V := v.shape.rdc)
    (R := (u.shape.paste v.shape k ψ).rdc) (C := (u.shape.boundary k true).rdc)
    (pasteInl u v k ψ) (pasteInr u v k ψ) u.map v.map
    (u.shape.boundaryIncl k true) d
    (fun y => ConcreteCategory.congr_hom hcond y) ?_ ?_
  · exact (map_comp _ _ _).trans ((congrArg (OGP.map (pasteInl u v k ψ))
      (u.shape.map_boundaryIncl_top k true)).trans
      ((map_boundary (pasteInl u v k ψ) ⊤ k true).trans hp.inf_eq_output.symm))
  · have hc : RDCpx.ofInclusion (P := (u.shape.boundary k true).rdc) (Q := u.shape.rdc)
        (u.shape.boundaryIncl k true) = u.shape.boundaryInclRDC k true := by
      ext _
      rfl
    have hd : RDCpx.ofInclusion (P := (u.shape.boundary k true).rdc) (Q := v.shape.rdc) d =
          (RDCpx.isoOfIso (P := (u.boundary k true).shape.rdc)
            (Q := (v.boundary k false).shape.rdc) ψ).hom ≫
            v.shape.boundaryInclRDC k false := by
      ext _
      rfl
    have hab₂ : realize.map (RDCpx.isoOfIso (P := (u.boundary k true).shape.rdc)
        (Q := (v.boundary k false).shape.rdc) ψ).hom ≫
          realize.map (v.shape.boundaryInclRDC k false) ≫ v.map =
        realize.map (u.shape.boundaryInclRDC k true) ≫ u.map := hab
    rw [hc, hd]
    exact hab₂.symm.trans (realize.map_comp_assoc _ _ _).symm

@[implicit_reducible, simps] noncomputable def pasteAlong
    (hab : realize.map (RDCpx.isoOfIso (P := (u.boundary k true).shape.rdc)
      (Q := (v.boundary k false).shape.rdc) ψ).hom ≫ (v.boundary k false).map =
        (u.boundary k true).map) : PastingDiagram X :=
  ⟨u.shape.paste v.shape k ψ,
    coverDesc (U := u.shape.rdc) (V := v.shape.rdc) (R := (u.shape.paste v.shape k ψ).rdc)
      (pasteInl u v k ψ) (pasteInr u v k ψ)
      (isPastingIn_paste u v k ψ).sup_eq
      u.map v.map (coverCompatible_paste u v k ψ hab)⟩

variable (hab : realize.map (RDCpx.isoOfIso (P := (u.boundary k true).shape.rdc)
      (Q := (v.boundary k false).shape.rdc) ψ).hom ≫ (v.boundary k false).map =
        (u.boundary k true).map)

theorem ofInclusion_pasteInl_map :
    realize.map (RDCpx.ofInclusion (P := u.shape.rdc) (Q := (u.shape.paste v.shape k ψ).rdc)
      (pasteInl u v k ψ)) ≫ (pasteAlong u v k ψ hab).map = u.map :=
  ofInclusion_coverDesc_left (U := u.shape.rdc) (V := v.shape.rdc)
    (R := (u.shape.paste v.shape k ψ).rdc) _ _ (isPastingIn_paste u v k ψ).sup_eq _ _ _

theorem ofInclusion_pasteInr_map :
    realize.map (RDCpx.ofInclusion (P := v.shape.rdc) (Q := (u.shape.paste v.shape k ψ).rdc)
      (pasteInr u v k ψ)) ≫ (pasteAlong u v k ψ hab).map = v.map :=
  ofInclusion_coverDesc_right (U := u.shape.rdc) (V := v.shape.rdc)
    (R := (u.shape.paste v.shape k ψ).rdc) _ _ (isPastingIn_paste u v k ψ).sup_eq _ _ _

omit hab in
theorem hom_ext_paste {Z : DiagSet.{u}}
    {m m' : realize.obj (u.shape.paste v.shape k ψ).rdc ⟶ Z}
    (h₁ : realize.map (RDCpx.ofInclusion (P := u.shape.rdc) (Q := (u.shape.paste v.shape k ψ).rdc)
      (pasteInl u v k ψ)) ≫ m =
      realize.map (RDCpx.ofInclusion (P := u.shape.rdc) (Q := (u.shape.paste v.shape k ψ).rdc)
        (pasteInl u v k ψ)) ≫ m')
    (h₂ : realize.map (RDCpx.ofInclusion (P := v.shape.rdc) (Q := (u.shape.paste v.shape k ψ).rdc)
      (pasteInr u v k ψ)) ≫ m =
      realize.map (RDCpx.ofInclusion (P := v.shape.rdc) (Q := (u.shape.paste v.shape k ψ).rdc)
        (pasteInr u v k ψ)) ≫ m') : m = m' :=
  hom_ext_cover (U := u.shape.rdc) (V := v.shape.rdc) (R := (u.shape.paste v.shape k ψ).rdc)
    _ _ (isPastingIn_paste u v k ψ).sup_eq h₁ h₂

theorem dim_pasteAlong : (pasteAlong u v k ψ hab).dim = max u.dim v.dim := by
  have hp := isPastingIn_paste u v k ψ
  have h : ((u.shape.paste v.shape k ψ).dimension : WithBot ℕ∞) =
      ((max u.dim v.dim : ℕ) : WithBot ℕ∞) := by
    rw [← (u.shape.paste v.shape k ψ).krullDim_eq_dimension, ← LowerSet.krullDim_top,
      ← hp.sup_eq, LowerSet.krullDim_sup, krullDim_map, krullDim_map,
      LowerSet.krullDim_top, LowerSet.krullDim_top, u.shape.krullDim_eq_dimension,
      v.shape.krullDim_eq_dimension, ← Nat.mono_cast.map_max, dim_def, dim_def]
  exact_mod_cast h

theorem equiv_boundary_pasteAlong (β : Bool) :
    ((pasteAlong u v k ψ hab).boundary k β).Equiv ((cond β v u).boundary k β) := by
  cases β
  · exact equiv_boundary_of_emb u (pasteAlong u v k ψ hab) (pasteInl u v k ψ)
      (ofInclusion_pasteInl_map u v k ψ hab)
      ((map_boundary (pasteInl u v k ψ) ⊤ k false).trans
        (isPastingIn_paste u v k ψ).boundary_input.symm)
  · exact equiv_boundary_of_emb v (pasteAlong u v k ψ hab) (pasteInr u v k ψ)
      (ofInclusion_pasteInr_map u v k ψ hab)
      ((map_boundary (pasteInr u v k ψ) ⊤ k true).trans
        (isPastingIn_paste u v k ψ).boundary_output.symm)

omit hab in
theorem equiv_pasteAlong {u v u' v' : PastingDiagram X} {k : ℕ}
    {ψ : (u.boundary k true).shape.ogp ≅ (v.boundary k false).shape.ogp}
    {ψ' : (u'.boundary k true).shape.ogp ≅ (v'.boundary k false).shape.ogp}
    {hab : realize.map (RDCpx.isoOfIso (P := (u.boundary k true).shape.rdc)
      (Q := (v.boundary k false).shape.rdc) ψ).hom ≫ (v.boundary k false).map =
        (u.boundary k true).map}
    {hab' : realize.map (RDCpx.isoOfIso (P := (u'.boundary k true).shape.rdc)
      (Q := (v'.boundary k false).shape.rdc) ψ').hom ≫ (v'.boundary k false).map =
        (u'.boundary k true).map}
    (hu : u.Equiv u') (hv : v.Equiv v') :
    (pasteAlong u v k ψ hab).Equiv (pasteAlong u' v' k ψ' hab') := by
  obtain ⟨α, hα⟩ := hu
  obtain ⟨β, hβ⟩ := hv
  have hp := isPastingIn_paste u v k ψ
  have hp' := isPastingIn_paste u' v' k ψ'
  let i' : u.shape.ogp ⟶ (u'.shape.paste v'.shape k ψ').ogp :=
    α.hom ≫ pasteInl u' v' k ψ'
  let j' : v.shape.ogp ⟶ (u'.shape.paste v'.shape k ψ').ogp :=
    β.hom ≫ pasteInr u' v' k ψ'
  have hi : OGP.map i' ⊤ = OGP.map (pasteInl u' v' k ψ') ⊤ := by
    rw [map_comp, map_top_of_isIso]
  have hj : OGP.map j' ⊤ = OGP.map (pasteInr u' v' k ψ') ⊤ := by
    rw [map_comp, map_top_of_isIso]
  have hp'' : (u'.shape.paste v'.shape k ψ').ogp.IsPastingIn k (OGP.map i' ⊤) (OGP.map j' ⊤) ⊤ := by
    rw [hi, hj]
    exact hp'
  obtain ⟨Θ, hΘ, -, -⟩ := exists_iso_of_covers (a := pasteAlong u' v' k ψ' hab')
    (b := pasteAlong u v k ψ hab)
    (C := (pasteAlong u' v' k ψ' hab').shape.rdc) (P := u.shape.rdc) (Q := v.shape.rdc)
    (pasteAlong u' v' k ψ' hab').map
    (𝟙 (pasteAlong u' v' k ψ' hab').shape.ogp)
    (by simp only [MoleculeShape.ofInclusion_id, realize.map_id, Category.id_comp])
    i' j' (hp''.sup_eq.trans (map_top_of_isIso _).symm) (pasteInl u v k ψ) (pasteInr u v k ψ)
    hp.sup_eq (apply_eq_apply_iff_of_isPastingIn_of_isMolecule u.shape.isMolecule hp'' hp)
    (by
      have hc : RDCpx.ofInclusion (P := u.shape.rdc) (Q := (u'.shape.paste v'.shape k ψ').rdc) i' =
          (RDCpx.isoOfIso (P := u.shape.rdc) (Q := u'.shape.rdc) α).hom ≫
            RDCpx.ofInclusion (P := u'.shape.rdc) (Q := (u'.shape.paste v'.shape k ψ').rdc)
              (pasteInl u' v' k ψ') := by
        ext x
        rfl
      rw [hc, realize.map_comp_assoc, ofInclusion_pasteInl_map u' v' k ψ' hab', hα,
        ofInclusion_pasteInl_map u v k ψ hab])
    (by
      have hc : RDCpx.ofInclusion (P := v.shape.rdc) (Q := (u'.shape.paste v'.shape k ψ').rdc) j' =
          (RDCpx.isoOfIso (P := v.shape.rdc) (Q := v'.shape.rdc) β).hom ≫
            RDCpx.ofInclusion (P := v'.shape.rdc) (Q := (u'.shape.paste v'.shape k ψ').rdc)
              (pasteInr u' v' k ψ') := by
        ext x
        rfl
      rw [hc, realize.map_comp_assoc, ofInclusion_pasteInr_map u' v' k ψ' hab', hβ,
        ofInclusion_pasteInr_map u v k ψ hab])
  exact Equiv.symm ⟨Θ, hΘ⟩

theorem mapTo_pasteAlong (f : X ⟶ Y)
    (hab' : realize.map (RDCpx.isoOfIso (P := ((u.mapTo f).boundary k true).shape.rdc)
      (Q := ((v.mapTo f).boundary k false).shape.rdc) ψ).hom ≫ ((v.mapTo f).boundary k false).map =
        ((u.mapTo f).boundary k true).map) :
    ((pasteAlong u v k ψ hab).mapTo f).Equiv
      (pasteAlong (u.mapTo f) (v.mapTo f) k ψ hab') := by
  refine ⟨Iso.refl _, ?_⟩
  change realize.map (𝟙 (u.shape.paste v.shape k ψ).rdc) ≫
      (pasteAlong (u.mapTo f) (v.mapTo f) k ψ hab').map = (pasteAlong u v k ψ hab).map ≫ f
  rw [realize.map_id, Category.id_comp]
  refine hom_ext_paste u v k ψ ?_ ?_
  · exact (ofInclusion_pasteInl_map (u.mapTo f) (v.mapTo f) k ψ hab').trans
      ((congrArg (· ≫ f) (ofInclusion_pasteInl_map u v k ψ hab)).symm.trans
        (Category.assoc _ _ _))
  · exact (ofInclusion_pasteInr_map (u.mapTo f) (v.mapTo f) k ψ hab').trans
      ((congrArg (· ≫ f) (ofInclusion_pasteInr_map u v k ψ hab)).symm.trans
        (Category.assoc _ _ _))

end Pasting

def Pastable (u v : PastingDiagram X) (k : ℕ) : Prop :=
  (u.boundary k true).Equiv (v.boundary k false) ∧ k < min u.dim v.dim

theorem Pastable.of_equiv {a b a' b' : PastingDiagram X} {n : ℕ} (hp : a.Pastable b n)
    (ea : a.Equiv a') (eb : b.Equiv b') : a'.Pastable b' n :=
  ⟨(ea.boundary n true).symm.trans (hp.1.trans (eb.boundary n false)),
    by rw [← dim_eq_of_equiv ea, ← dim_eq_of_equiv eb]; exact hp.2⟩

theorem Pastable.mapTo {u v : PastingDiagram X} {k : ℕ} (h : u.Pastable v k)
    (f : X ⟶ Y) : (u.mapTo f).Pastable (v.mapTo f) k :=
  ⟨h.1.boundary_mapTo f, h.2⟩

theorem Pastable.of_mapTo {u v : PastingDiagram X} {k : ℕ} (f : X ⟶ Y) [Mono f]
    (h : (u.mapTo f).Pastable (v.mapTo f) k) : u.Pastable v k :=
  ⟨Equiv.of_mapTo f (by rw [← boundary_mapTo, ← boundary_mapTo]; exact h.1), h.2⟩

theorem Pastable.of_side {c h : PastingDiagram X} {n : ℕ} (α : Bool)
    (he : (c.boundary n α).Equiv (h.boundary n (!α))) (hc : n < c.dim) (hh : n < h.dim) :
    (cond α c h).Pastable (cond α h c) n := by
  cases α
  · exact ⟨he.symm, lt_min hh hc⟩
  · exact ⟨he, lt_min hc hh⟩

theorem Pastable.side {c h : PastingDiagram X} {n : ℕ} {α : Bool}
    (hp : (cond α c h).Pastable (cond α h c) n) : (c.boundary n α).Equiv (h.boundary n (!α)) := by
  cases α
  · exact hp.1.symm
  · exact hp.1

@[implicit_reducible] noncomputable def paste (u v : PastingDiagram X) (k : ℕ)
    (h : u.Pastable v k) : PastingDiagram X :=
  pasteAlong u v k h.1.iso h.1.map_comm

theorem equiv_boundary_paste {x y : PastingDiagram X} {n : ℕ} (h : x.Pastable y n) (β : Bool) :
    ((x.paste y n h).boundary n β).Equiv ((cond β y x).boundary n β) :=
  equiv_boundary_pasteAlong x y n _ h.1.map_comm β

theorem dim_paste (u v : PastingDiagram X) (k : ℕ) (h : u.Pastable v k) :
    (u.paste v k h).dim = max u.dim v.dim :=
  dim_pasteAlong u v k _ h.1.map_comm

theorem dim_paste_cond {c h : PastingDiagram X} {n : ℕ} {α : Bool}
    (hp : (cond α c h).Pastable (cond α h c) n) :
    ((cond α c h).paste (cond α h c) n hp).dim = max c.dim h.dim := by
  rw [dim_paste]
  cases α
  · exact max_comm _ _
  · rfl

theorem equiv_paste_of_emb (u v a : PastingDiagram X) (k : ℕ) (h : u.Pastable v k)
    {C : RDCpx.{0}} (w : realize.obj C ⟶ X)
    (f : a.shape.ogp ⟶ C.obj.toOGP) (i : u.shape.ogp ⟶ C.obj.toOGP)
    (j : v.shape.ogp ⟶ C.obj.toOGP) [IsInclusion f] [IsInclusion i] [IsInclusion j]
    (hf : realize.map (RDCpx.ofInclusion (P := a.shape.rdc) (Q := C) f) ≫ w = a.map)
    (hi : realize.map (RDCpx.ofInclusion (P := u.shape.rdc) (Q := C) i) ≫ w = u.map)
    (hj : realize.map (RDCpx.ofInclusion (P := v.shape.rdc) (Q := C) j) ≫ w = v.map)
    (hp : C.obj.toOGP.IsPastingIn k (OGP.map i ⊤) (OGP.map j ⊤) (OGP.map f ⊤)) :
    (u.paste v k h).Equiv a := by
  obtain ⟨e, he⟩ := exists_iso_restrict f rfl
  have he' : e.inv ≫ f = incl (OGP.map f ⊤) := (Iso.inv_comp_eq e).2 he.symm
  have hi' : ∀ x, i x ∈ OGP.map f ⊤ := fun x =>
    hp.sup_eq ▸ LowerSet.mem_sup_iff.2 (Or.inl ⟨x, LowerSet.mem_top, rfl⟩)
  have hj' : ∀ y, j y ∈ OGP.map f ⊤ := fun y =>
    hp.sup_eq ▸ LowerSet.mem_sup_iff.2 (Or.inr ⟨y, LowerSet.mem_top, rfl⟩)
  let i' : u.shape.ogp ⟶ a.shape.ogp := codRestrict i (OGP.map f ⊤) hi' ≫ e.inv
  let j' : v.shape.ogp ⟶ a.shape.ogp := codRestrict j (OGP.map f ⊤) hj' ≫ e.inv
  have hfi_hom : i' ≫ f = i := by
    rw [Category.assoc, he', codRestrict_incl]
  have hfj_hom : j' ≫ f = j := by
    rw [Category.assoc, he', codRestrict_incl]
  have hfi (x : u.shape.ogp) : f (i' x) = i x := ConcreteCategory.congr_hom hfi_hom x
  have hfj (y : v.shape.ogp) : f (j' y) = j y := ConcreteCategory.congr_hom hfj_hom y
  have hp' : a.shape.ogp.IsPastingIn k (OGP.map i' ⊤) (OGP.map j' ⊤) ⊤ := by
    refine (isPastingIn_map_iff f k _ _ _).1 ?_
    rwa [← map_comp, ← map_comp, hfi_hom, hfj_hom]
  have hq := isPastingIn_paste u v k h.1.iso
  obtain ⟨Θ, hΘ, -, -⟩ := exists_iso_of_covers (a := a) (b := u.paste v k h)
    (C := C) (P := u.shape.rdc) (Q := v.shape.rdc) w f hf i j hp.sup_eq
    (pasteInl u v k h.1.iso) (pasteInr u v k h.1.iso) hq.sup_eq
    (fun (x : u.shape.ogp) (y : v.shape.ogp) => by
      change i x = j y ↔ _
      rw [← hfi, ← hfj, (IsInclusion.injective (f := f)).eq_iff]
      exact apply_eq_apply_iff_of_isPastingIn_of_isMolecule u.shape.isMolecule hp' hq x y)
    (hi.trans (ofInclusion_pasteInl_map u v k h.1.iso h.1.map_comm).symm)
    (hj.trans (ofInclusion_pasteInr_map u v k h.1.iso h.1.map_comm).symm)
  exact Equiv.symm ⟨Θ, hΘ⟩

theorem Equiv.paste {u u' v v' : PastingDiagram X} {k : ℕ} (hu : u.Equiv u') (hv : v.Equiv v')
    (h : u.Pastable v k) (h' : u'.Pastable v' k) : (u.paste v k h).Equiv (u'.paste v' k h') :=
  equiv_pasteAlong hu hv

theorem paste_mapTo (u v : PastingDiagram X) (k : ℕ) (h : u.Pastable v k) (f : X ⟶ Y)
    (h' : (u.mapTo f).Pastable (v.mapTo f) k) :
    ((u.paste v k h).mapTo f).Equiv ((u.mapTo f).paste (v.mapTo f) k h') := by
  have hab := h.1.map_comm
  have hab' : realize.map (RDCpx.isoOfIso (P := ((u.mapTo f).boundary k true).shape.rdc)
      (Q := ((v.mapTo f).boundary k false).shape.rdc) h.1.iso).hom ≫
        ((v.mapTo f).boundary k false).map = ((u.mapTo f).boundary k true).map := by
    change realize.map (RDCpx.isoOfIso (P := ((u.mapTo f).boundary k true).shape.rdc)
        (Q := ((v.mapTo f).boundary k false).shape.rdc) h.1.iso).hom ≫
          realize.map (v.shape.boundaryInclRDC k false) ≫ v.map ≫ f =
        realize.map (u.shape.boundaryInclRDC k true) ≫ u.map ≫ f
    have hab₂ : realize.map (RDCpx.isoOfIso (P := (u.boundary k true).shape.rdc)
        (Q := (v.boundary k false).shape.rdc) h.1.iso).hom ≫
          realize.map (v.shape.boundaryInclRDC k false) ≫ v.map =
        realize.map (u.shape.boundaryInclRDC k true) ≫ u.map := hab
    exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))).symm.trans
      ((congrArg (· ≫ f) hab₂).trans (Category.assoc _ _ _))
  exact (mapTo_pasteAlong u v k _ hab f hab').trans
    (equiv_pasteAlong (.refl _) (.refl _))

end Atoms.Diagrammatic.PastingDiagram

namespace Atoms.Diagrammatic

def Pastes {X : DiagSet.{u}} (u v : PastingDiagram X) (k : ℕ) (w : PastingDiagram X) : Prop :=
  (∃ h : u.Pastable v k, w.Equiv (u.paste v k h)) ∨
    ∃ γ, (cond γ v u).dim ≤ k ∧ (cond γ v u).Equiv ((cond γ u v).boundary k γ) ∧
      w.Equiv (cond γ u v)

namespace Pastes

open PastingDiagram

variable {X Y : DiagSet.{u}} {u v w u' v' w' : PastingDiagram X} {k : ℕ}

theorem of_equiv (h : Pastes u v k w) (eu : u.Equiv u') (ev : v.Equiv v') (ew : w.Equiv w') :
    Pastes u' v' k w' := by
  rcases h with ⟨hp, hw⟩ | ⟨γ, hd, hu, hw⟩
  · have hp' := hp.of_equiv eu ev
    exact Or.inl ⟨hp', ew.symm.trans (hw.trans (Equiv.paste eu ev hp hp'))⟩
  · exact Or.inr ⟨γ, by rw [← dim_eq_of_equiv (ev.cond γ eu)]; exact hd,
      (ev.cond γ eu).symm.trans (hu.trans ((eu.cond γ ev).boundary k γ)),
      ew.symm.trans (hw.trans (eu.cond γ ev))⟩

theorem unique (h : Pastes u v k w) (h' : Pastes u v k w') : w.Equiv w' := by
  have hmin (γ : Bool) : min u.dim v.dim ≤ (cond γ v u).dim :=
    Bool.cond_rec_prop (p := fun x : PastingDiagram X => _ ≤ x.dim) γ (min_le_right _ _)
      (min_le_left _ _)
  rcases h with ⟨hp, hw⟩ | ⟨γ, hd, hu, hw⟩ <;> rcases h' with ⟨hp', hw'⟩ | ⟨γ', hd', hu', hw'⟩
  · exact hw.trans ((Equiv.paste (.refl _) (.refl _) hp hp').trans (hw'.symm))
  · exact absurd hp.2 (by have := hmin γ'; omega)
  · exact absurd hp'.2 (by have := hmin γ; omega)
  · obtain rfl | rfl := Bool.eq_or_eq_not γ' γ
    · exact hw.trans hw'.symm
    · rw [Bool.cond_not] at hd' hw'
      exact hw.trans ((equiv_boundary_dim _ hd' γ).symm.trans (hu.symm.trans hw'.symm))

theorem mapTo (h : Pastes u v k w) (f : X ⟶ Y) : Pastes (u.mapTo f) (v.mapTo f) k (w.mapTo f) := by
  rcases h with ⟨hp, hw⟩ | ⟨γ, hd, hu, hw⟩
  · exact Or.inl ⟨hp.mapTo f, (hw.mapTo f).trans (paste_mapTo u v k hp f (hp.mapTo f))⟩
  · refine Or.inr ⟨γ, ?_⟩
    rw [← Bool.apply_cond (PastingDiagram.mapTo · f), ← Bool.apply_cond (PastingDiagram.mapTo · f),
      boundary_mapTo]
    exact ⟨hd, hu.mapTo f, hw.mapTo f⟩

end Pastes

end Atoms.Diagrammatic
