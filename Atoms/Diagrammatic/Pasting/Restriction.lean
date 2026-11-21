import Atoms.Diagrammatic.Pasting.Paste
import Atoms.Molecule.Rewritable.Basic

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Order Atoms.Shape

universe u

namespace Atoms.Diagrammatic.PastingDiagram

variable {X Y : DiagSet.{u}}

@[implicit_reducible, simps]
def restrictTo (u : PastingDiagram X) {S : LowerSet u.shape.ogp} [DecidablePred (· ∈ S)]
    (hS : IsMoleculeIn u.shape.ogp S) : PastingDiagram X :=
  ⟨u.shape.sub hS,
    realize.map
      (RDCpx.ofInclusion (P := (u.shape.sub hS).rdc) (Q := u.shape.rdc) (u.shape.subIncl hS)) ≫
        u.map⟩

section Restrict

variable (u : PastingDiagram X) {S : LowerSet u.shape.ogp} [DecidablePred (· ∈ S)]
  (hS : IsMoleculeIn u.shape.ogp S)

theorem dim_restrictTo : ((u.restrictTo hS).dim : WithBot ℕ∞) = krullDim S :=
  u.shape.dimension_sub hS

theorem isRound_restrictTo_iff : (u.restrictTo hS).IsRound ↔ u.shape.ogp.IsRound S :=
  u.shape.isRound_sub_iff hS

theorem boundary_eq_restrictTo (k : ℕ) (α : Bool) :
    u.boundary k α = u.restrictTo (u.shape.isMolecule.boundary k α) :=
  rfl

end Restrict

section Ambient

theorem map_comp_of_emb (a b : PastingDiagram X) {c : PastingDiagram X}
    (f : a.shape.ogp ⟶ b.shape.ogp) (g : b.shape.ogp ⟶ c.shape.ogp)
    [IsInclusion f] [IsInclusion g]
    (hf : realize.map (RDCpx.ofInclusion (P := a.shape.rdc) (Q := b.shape.rdc) f) ≫ b.map = a.map)
    (hg : realize.map (RDCpx.ofInclusion (P := b.shape.rdc) (Q := c.shape.rdc) g) ≫ c.map = b.map) :
    realize.map (RDCpx.ofInclusion (P := a.shape.rdc) (Q := c.shape.rdc)
      (f ≫ g : a.shape.ogp ⟶ c.shape.ogp)) ≫ c.map = a.map := by
  have hcomp : RDCpx.ofInclusion (P := a.shape.rdc) (Q := c.shape.rdc)
      (f ≫ g : a.shape.ogp ⟶ c.shape.ogp) =
      RDCpx.ofInclusion (P := a.shape.rdc) (Q := b.shape.rdc) f ≫
        RDCpx.ofInclusion (P := b.shape.rdc) (Q := c.shape.rdc) g := by
    ext x
    rfl
  rw [hcomp, realize.map_comp_assoc, hg, hf]

theorem boundary_comm (u : PastingDiagram X) (k : ℕ) (α : Bool) :
    realize.map (RDCpx.ofInclusion (P := (u.shape.boundary k α).rdc) (Q := u.shape.rdc)
      (u.shape.boundaryIncl k α)) ≫ u.map = (u.boundary k α).map :=
  rfl

theorem equiv_restrictTo_of_emb (a : PastingDiagram X) {u : PastingDiagram X}
    (f : a.shape.ogp ⟶ u.shape.ogp) [IsInclusion f]
    (hf : realize.map (RDCpx.ofInclusion (P := a.shape.rdc) (Q := u.shape.rdc) f) ≫ u.map = a.map)
    {S : LowerSet u.shape.ogp} [DecidablePred (· ∈ S)] (him : OGP.map f ⊤ = S)
    (hS : IsMoleculeIn u.shape.ogp S) : a.Equiv (u.restrictTo hS) :=
  equiv_of_emb_of_image_eq u.map f (u.shape.subIncl hS) hf rfl
    (him.trans (u.shape.map_subIncl_top hS).symm)

theorem equiv_restrictTo_of_eq (u : PastingDiagram X) {S T : LowerSet u.shape.ogp}
    [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (hS : IsMoleculeIn u.shape.ogp S) (hT : IsMoleculeIn u.shape.ogp T) (h : S = T) :
    (u.restrictTo hS).Equiv (u.restrictTo hT) :=
  equiv_restrictTo_of_emb (u.restrictTo hS) (u.shape.subIncl hS) rfl
    ((u.shape.map_subIncl_top hS).trans h) hT

theorem equiv_restrictTo_restrictTo (u : PastingDiagram X) {S : LowerSet u.shape.ogp}
    [DecidablePred (· ∈ S)] (hS : IsMoleculeIn u.shape.ogp S)
    {T : LowerSet (u.shape.sub hS).ogp} [DecidablePred (· ∈ T)]
    (hT : IsMoleculeIn (u.shape.sub hS).ogp T)
    {T' : LowerSet u.shape.ogp} [DecidablePred (· ∈ T')]
    (him : OGP.map (u.shape.subIncl hS) T = T') (hT' : IsMoleculeIn u.shape.ogp T') :
    ((u.restrictTo hS).restrictTo hT).Equiv (u.restrictTo hT') :=
  equiv_restrictTo_of_emb ((u.restrictTo hS).restrictTo hT)
    ((u.shape.sub hS).subIncl hT ≫ u.shape.subIncl hS)
    (map_comp_of_emb ((u.restrictTo hS).restrictTo hT) (u.restrictTo hS)
      ((u.shape.sub hS).subIncl hT) (u.shape.subIncl hS) rfl rfl)
    (by rw [map_comp, (u.shape.sub hS).map_subIncl_top, him]) hT'

theorem equiv_boundary_restrictTo (u : PastingDiagram X) {S : LowerSet u.shape.ogp}
    [DecidablePred (· ∈ S)] (hS : IsMoleculeIn u.shape.ogp S) (k : ℕ) (α : Bool) :
    ((u.restrictTo hS).boundary k α).Equiv
      (u.restrictTo (hS.boundary k α)) := by
  rw [boundary_eq_restrictTo]
  exact equiv_restrictTo_restrictTo u hS _
    ((map_boundary (u.shape.subIncl hS) ⊤ k α).trans (by rw [u.shape.map_subIncl_top])) _

theorem equiv_restrictTo_univ (u : PastingDiagram X) :
    (u.restrictTo u.shape.isMolecule).Equiv u :=
  (equiv_restrictTo_of_emb u (𝟙 u.shape.ogp)
    (by simp only [MoleculeShape.ofInclusion_id, realize.map_id, Category.id_comp])
    (map_top_of_isIso _) u.shape.isMolecule).symm

end Ambient

structure Within (a m : PastingDiagram X) where
  emb : a.shape.ogp ⟶ m.shape.ogp
  [isInclusion : IsInclusion emb]
  comm : realize.map (RDCpx.ofInclusion (P := a.shape.rdc) (Q := m.shape.rdc) emb) ≫ m.map = a.map

attribute [instance] Within.isInclusion

namespace Within

variable {a b m n : PastingDiagram X}

def image (w : Within a m) : LowerSet m.shape.ogp := OGP.map w.emb ⊤

instance (w : Within a m) : DecidablePred (· ∈ w.image) :=
  inferInstanceAs (DecidablePred (· ∈ OGP.map w.emb ⊤))

theorem mem_image_apply (w : Within a m) (x : a.shape.ogp) : w.emb x ∈ w.image :=
  ⟨x, LowerSet.mem_top, rfl⟩

theorem isMoleculeIn_image (w : Within a m) : IsMoleculeIn m.shape.ogp w.image :=
  (isMoleculeIn_map_iff w.emb (U := ⊤)).2 a.shape.isMolecule

theorem krullDim_image (w : Within a m) : krullDim w.image = a.dim := by
  rw [image, krullDim_map, LowerSet.krullDim_top, a.shape.krullDim_eq_dimension, dim_def]

theorem round_image_iff (w : Within a m) : m.shape.ogp.IsRound w.image ↔ a.IsRound :=
  isRound_map_iff w.emb (U := ⊤)

theorem boundary_image (w : Within a m) (k : ℕ) (α : Bool) :
    m.shape.ogp.boundary w.image k α = OGP.map w.emb (a.shape.ogp.boundary ⊤ k α) :=
  (map_boundary w.emb ⊤ k α).symm

def refl (a : PastingDiagram X) : Within a a :=
  ⟨𝟙 a.shape.ogp, by simp only [MoleculeShape.ofInclusion_id, realize.map_id, Category.id_comp]⟩

theorem image_refl (a : PastingDiagram X) : (refl a).image = ⊤ :=
  map_top_of_isIso (𝟙 a.shape.ogp)

noncomputable def ofEquiv (h : a.Equiv b) : Within a b := ⟨h.iso.hom, h.map_comm⟩

theorem image_ofEquiv (h : a.Equiv b) : (ofEquiv h).image = ⊤ :=
  map_top_of_isIso h.iso.hom

def trans (w : Within a m) (w' : Within m n) : Within a n :=
  ⟨w.emb ≫ w'.emb, map_comp_of_emb a m w.emb w'.emb w.comm w'.comm⟩

theorem image_trans (w : Within a m) (w' : Within m n) :
    (w.trans w').image = OGP.map w'.emb w.image :=
  map_comp w.emb w'.emb ⊤

theorem image_trans_assoc {a m₁ m₂ m₃ : PastingDiagram X} (w₁ : Within a m₁)
    (w₂ : Within m₁ m₂) (w₃ : Within m₂ m₃) :
    (w₁.trans (w₂.trans w₃)).image = OGP.map w₃.emb (w₁.trans w₂).image := by
  rw [image_trans, image_trans]
  exact map_comp w₂.emb w₃.emb w₁.image

def restrictTo (m : PastingDiagram X) {S : LowerSet m.shape.ogp} [DecidablePred (· ∈ S)]
    (hS : IsMoleculeIn m.shape.ogp S) : Within (m.restrictTo hS) m :=
  ⟨m.shape.subIncl hS, rfl⟩

theorem image_restrictTo (m : PastingDiagram X) {S : LowerSet m.shape.ogp} [DecidablePred (· ∈ S)]
    (hS : IsMoleculeIn m.shape.ogp S) : (restrictTo m hS).image = S :=
  m.shape.map_subIncl_top hS

def boundary (a : PastingDiagram X) (k : ℕ) (α : Bool) : Within (a.boundary k α) a :=
  ⟨a.shape.boundaryIncl k α, boundary_comm a k α⟩

theorem image_boundary (a : PastingDiagram X) (k : ℕ) (α : Bool) :
    (boundary a k α).image = a.shape.ogp.boundary ⊤ k α :=
  a.shape.map_boundaryIncl_top k α

theorem image_boundary_trans (w : Within a m) (k : ℕ) (α : Bool) :
    ((boundary a k α).trans w).image = m.shape.ogp.boundary w.image k α := by
  rw [image_trans, image_boundary, w.boundary_image]

theorem equiv_restrictTo_of_eq (w : Within a m) {S : LowerSet m.shape.ogp} [DecidablePred (· ∈ S)]
    (h : w.image = S) (hS : IsMoleculeIn m.shape.ogp S) : a.Equiv (m.restrictTo hS) :=
  equiv_restrictTo_of_emb a w.emb w.comm h hS

theorem equiv_of_image_eq (w : Within a m) (w' : Within b m) (h : w.image = w'.image) :
    a.Equiv b :=
  equiv_of_emb_of_image_eq m.map w.emb w'.emb w.comm w'.comm h

theorem emb_apply_eq_of_image_eq (w w' : Within a m) (h : w.image = w'.image)
    (x : a.shape.ogp) : w.emb x = w'.emb x :=
  IsMoleculeIn.eqOn_of_map_eq w.emb w'.emb a.shape.isMolecule h (LowerSet.mem_top (a := x))

theorem ext_of_image_eq (w w' : Within a m) (h : w.image = w'.image) : w = w' := by
  have he : w.emb = w'.emb := by
    ext x
    exact emb_apply_eq_of_image_eq w w' h x
  cases w with
  | mk e hc =>
    cases w' with
    | mk e' hc' =>
      change e = e' at he
      subst he
      rfl

theorem trans_assoc {a m₁ m₂ m₃ : PastingDiagram X} (w₁ : Within a m₁)
    (w₂ : Within m₁ m₂) (w₃ : Within m₂ m₃) : (w₁.trans w₂).trans w₃ = w₁.trans (w₂.trans w₃) :=
  ext_of_image_eq _ _ ((image_trans _ _).trans (image_trans_assoc _ _ _).symm)

private def ofImageLEFun (w : Within a m) (w' : Within b m) (h : w.image ≤ w'.image)
    (x : a.shape.ogp) : b.shape.ogp :=
  (IsInclusion.injective (f := w'.emb)).invOfMemRange
    ⟨w.emb x, by obtain ⟨y, -, hy⟩ := h (w.mem_image_apply x); exact ⟨y, hy⟩⟩

private theorem emb_ofImageLEFun (w : Within a m) (w' : Within b m) (h : w.image ≤ w'.image)
    (x : a.shape.ogp) : w'.emb (ofImageLEFun w w' h x) = w.emb x :=
  (IsInclusion.injective (f := w'.emb)).left_inv_of_invOfMemRange _

def ofImageLE (w : Within a m) (w' : Within b m) (h : w.image ≤ w'.image) : Within a b where
  emb := ConcreteCategory.ofHom ⟨ofImageLEFun w w' h,
    IsMorphism.of_comp_of_injective (g := w'.emb) (isMorphism w'.emb) IsInclusion.injective
      ((funext (emb_ofImageLEFun w w' h) : (w'.emb ∘ ofImageLEFun w w' h) = w.emb) ▸
        isMorphism w.emb)⟩
  isInclusion := ⟨fun x y hxy => IsInclusion.injective (f := w.emb) (by
    change ofImageLEFun w w' h x = ofImageLEFun w w' h y at hxy
    rw [← emb_ofImageLEFun w w' h x, ← emb_ofImageLEFun w w' h y, hxy])⟩
  comm := by
    rw [← w'.comm, ← realize.map_comp_assoc, ← w.comm]
    congr 2
    ext x
    exact emb_ofImageLEFun w w' h x

theorem ofImageLE_trans (w : Within a m) (w' : Within b m) (h : w.image ≤ w'.image) :
    (w.ofImageLE w' h).trans w' = w :=
  ext_of_image_eq _ _ (by
    rw [image_trans]
    refine SetLike.coe_injective ?_
    rw [coe_map, image, image, coe_map, coe_map, ← Set.image_comp]
    exact Set.image_congr fun x _ => emb_ofImageLEFun w w' h x)

theorem image_ofImageLE_trans (w : Within a m) (w' : Within b m) (h : w.image ≤ w'.image) :
    ((w.ofImageLE w' h).trans w').image = w.image := by
  rw [ofImageLE_trans]

def cond (α : Bool) (w₁ : Within a m) (w₂ : Within b m) : Within (_root_.cond α a b) m :=
  match α with
  | true => w₁
  | false => w₂

theorem image_cond (α : Bool) (w₁ : Within a m) (w₂ : Within b m) :
    (cond α w₁ w₂).image = _root_.cond α w₁.image w₂.image := by
  cases α <;> rfl

theorem isSubmoleculeOf_image_refl (a : PastingDiagram X) :
    a.shape.ogp.IsSubmoleculeOf (refl a).image ⊤ := by
  rw [image_refl]
  exact IsSubmoleculeOf.refl a.shape.isMolecule

theorem isSubmoleculeOf_image_trans {w : Within a m} {w' : Within m n}
    (hw : m.shape.ogp.IsSubmoleculeOf w.image ⊤)
    (hw' : n.shape.ogp.IsSubmoleculeOf w'.image ⊤) :
    n.shape.ogp.IsSubmoleculeOf (w.trans w').image ⊤ := by
  rw [image_trans]
  exact ((isSubmoleculeOf_map_iff w'.emb).2 hw).trans hw'

theorem isSubmoleculeOf_image_trans_ofEquiv_iff (w : Within a m) (h : m.Equiv n) :
    n.shape.ogp.IsSubmoleculeOf (w.trans (ofEquiv h)).image ⊤ ↔
      m.shape.ogp.IsSubmoleculeOf w.image ⊤ := by
  rw [image_trans, ← map_top_of_isIso h.iso.hom]
  exact isSubmoleculeOf_map_iff h.iso.hom

theorem isSubmoleculeOf_image_restrictTo (m : PastingDiagram X) {S : LowerSet m.shape.ogp}
    [DecidablePred (· ∈ S)] (hS : m.shape.ogp.IsSubmoleculeOf S ⊤) :
    m.shape.ogp.IsSubmoleculeOf (restrictTo m hS.isMoleculeIn).image ⊤ := by
  rw [image_restrictTo]
  exact hS

theorem isRewritableSubmolecule_image_iff (w : Within a m) :
    m.shape.ogp.IsRewritableSubmolecule w.image ⊤ ↔
      m.shape.ogp.IsSubmoleculeOf w.image ⊤ ∧ a.IsRound ∧ a.dim = m.dim := by
  rw [isRewritableSubmolecule_iff, w.round_image_iff, w.krullDim_image,
    LowerSet.krullDim_top, m.shape.krullDim_eq_dimension,
    Nat.cast_inj (R := WithBot ℕ∞)]
  exact and_congr_right fun _ => and_comm

theorem isRewritableSubmolecule_image_trans {w : Within a m} {w' : Within m n}
    (hw : m.shape.ogp.IsRewritableSubmolecule w.image ⊤)
    (hw' : n.shape.ogp.IsRewritableSubmolecule w'.image ⊤) :
    n.shape.ogp.IsRewritableSubmolecule (w.trans w').image ⊤ := by
  rw [isRewritableSubmolecule_image_iff] at hw hw' ⊢
  exact ⟨isSubmoleculeOf_image_trans hw.1 hw'.1, hw.2.1, hw.2.2.trans hw'.2.2⟩

theorem dim_eq_of_isRewritableSubmolecule_boundary {u : PastingDiagram X} {n : ℕ} {α : Bool}
    {ι : Within a (u.boundary n α)}
    (hι : (u.boundary n α).shape.ogp.IsRewritableSubmolecule ι.image ⊤)
    (hn : n ≤ u.dim) : a.dim = n :=
  (ι.isRewritableSubmolecule_image_iff.1 hι).2.2.trans (dim_boundary u hn α)

theorem isRewritableSubmolecule_image_trans_ofEquiv_iff (w : Within a m) (h : m.Equiv n) :
    n.shape.ogp.IsRewritableSubmolecule (w.trans (ofEquiv h)).image ⊤ ↔
      m.shape.ogp.IsRewritableSubmolecule w.image ⊤ := by
  rw [isRewritableSubmolecule_image_iff, isRewritableSubmolecule_image_iff,
    isSubmoleculeOf_image_trans_ofEquiv_iff, dim_eq_of_equiv h]

end Within

section Cells

variable (u : PastingDiagram X)

def cellAt (x : u.shape.ogp) : diagram X (principalAtomRDC u.shape.rdc x) :=
  u.map.app (op (principalAtomRDC u.shape.rdc x)) ⟨principalInclusionRDC u.shape.rdc x⟩

theorem ofCell_cellAt_map (x : u.shape.ogp) :
    (PastingDiagram.ofCell (u.cellAt x)).map =
      realize.map (principalInclusionRDC u.shape.rdc x) ≫ u.map := by
  ext ⟨T⟩ ⟨g : atomToRDCpx.obj T ⟶ atomToRDCpx.obj (principalAtomRDC u.shape.rdc x)⟩
  let g₀ : T ⟶ principalAtomRDC u.shape.rdc x := Atom.fullyFaithful.preimage g
  change X.map g₀.op (u.map.app _ ⟨principalInclusionRDC u.shape.rdc x⟩) =
    u.map.app (op T) ⟨g ≫ principalInclusionRDC u.shape.rdc x⟩
  exact (NatTrans.naturality_apply u.map g₀.op ⟨principalInclusionRDC u.shape.rdc x⟩).symm

def principalEmb (x : u.shape.ogp) :
    (principalAtomRDC u.shape.rdc x).ogp ⟶ u.shape.ogp :=
  principalInclusionOGP u.shape.rdc x

instance (x : u.shape.ogp) : IsInclusion (u.principalEmb x) :=
  ⟨IsInclusion.injective (f := principalInclusionOGP u.shape.rdc x)⟩

theorem image_principalEmb (x : u.shape.ogp) :
    OGP.map (u.principalEmb x) ⊤ = LowerSet.Iic x := by
  change OGP.map (principalInclusionOGP u.shape.rdc x) ⊤ = LowerSet.Iic x
  rw [map_comp, map_top_of_isIso, map_incl_top]

noncomputable def locatedCell (p : PastingDiagram X) (x : p.shape.ogp) :
    Within (ofCell (p.cellAt x)) p :=
  ⟨p.principalEmb x, by
    rw [ofCell_cellAt_map]
    exact congrArg (fun φ => realize.map φ ≫ p.map) (by ext; rfl)⟩

theorem equiv_ofCell_cellAt (x : u.shape.ogp) :
    (PastingDiagram.ofCell (u.cellAt x)).Equiv
      (u.restrictTo ((u.shape.isMolecule.isAtomIn_Iic (LowerSet.mem_top (a := x))).1)) :=
  equiv_restrictTo_of_emb (PastingDiagram.ofCell (u.cellAt x)) (u.principalEmb x)
    (u.ofCell_cellAt_map x).symm (u.image_principalEmb x) _

theorem equiv_ofCell_map_iso {U V : Atom} (e : U ≅ V) (x : diagram X V) :
    (PastingDiagram.ofCell (X.map e.hom.op x)).Equiv (PastingDiagram.ofCell x) := by
  refine ⟨Atom.isoOGP e, ?_⟩
  have e₁ : realize.map (RDCpx.isoOfIso (P := U.toMoleculeShape.rdc) (Q := V.toMoleculeShape.rdc)
      (Atom.isoOGP e)).hom ≫ (realizeAtomIso V).hom =
        (realizeAtomIso U).hom ≫ uliftYoneda.{u}.map e.hom := by
    ext ⟨T⟩ g
    rfl
  change realize.map (RDCpx.isoOfIso (P := U.toMoleculeShape.rdc) (Q := V.toMoleculeShape.rdc)
      (Atom.isoOGP e)).hom ≫ (realizeAtomIso V).hom ≫ uliftYonedaEquiv.symm x =
    (realizeAtomIso U).hom ≫ uliftYonedaEquiv.symm (X.map e.hom.op x)
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ uliftYonedaEquiv.symm x) e₁).trans
    ((Category.assoc _ _ _).trans (congrArg ((realizeAtomIso U).hom ≫ ·)
      ((uliftYonedaEquiv_symm_map e.hom.op x).symm))))

theorem exists_equiv_ofCell_of_dim_eq_zero {v : PastingDiagram Y} (hv : v.dim = 0) :
    ∃ y : diagram Y atomPoint, v.Equiv (ofCell y) := by
  obtain ⟨x, -, hx⟩ := v.shape.isMolecule.exists_eq_Iic_of_krullDim_eq_zero (by
    rw [LowerSet.krullDim_top, v.shape.krullDim_eq_dimension, ← dim_def, hv, Nat.cast_zero])
  have e₁ : v.Equiv (ofCell (v.cellAt x)) :=
    Within.equiv_of_image_eq (Within.refl v) (locatedCell v x) (by
      rw [Within.image_refl, hx]; exact (image_principalEmb v x).symm)
  have hA : (principalAtomRDC v.shape.rdc x).dimension = 0 := (dim_eq_of_equiv e₁).symm.trans hv
  have := isIso_toAtomPoint_of_dimension_eq_zero hA
  let e := asIso (toAtomPoint (principalAtomRDC v.shape.rdc x))
  refine ⟨Y.map e.inv.op (v.cellAt x), e₁.trans ?_⟩
  have h : Y.map e.hom.op (Y.map e.inv.op (v.cellAt x)) = v.cellAt x := by
    rw [← Functor.map_comp_apply, ← op_comp, Iso.hom_inv_id, op_id, Functor.map_id_apply]
  have e₂ := equiv_ofCell_map_iso e (Y.map e.inv.op (v.cellAt x))
  rwa [h] at e₂

end Cells

end Atoms.Diagrammatic.PastingDiagram
