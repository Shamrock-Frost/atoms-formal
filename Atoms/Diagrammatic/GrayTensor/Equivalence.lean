import Atoms.Diagrammatic.GrayTensor.Context
import Atoms.Diagrammatic.GrayTensor.Monoidal
import Atoms.Diagrammatic.Context.TrimSideInverse
import Atoms.Diagrammatic.Equivalence.GenPasting
import Atoms.Diagrammatic.Equivalence.TopCells
import Atoms.Diagrammatic.Marked.GrayTensor
import Atoms.Diagrammatic.Marked.InvertorTransport

open CategoryTheory Limits Opposite Order Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape
open Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Molecule.OGP

variable {P Q : OGP.{u}}

theorem IsGenPastingIn.of_map (f : P ⟶ Q) [IsInclusion f] {k : ℕ} {A B : LowerSet P}
    (h : Q.IsGenPastingIn k (OGP.map f A) (OGP.map f B)) : P.IsGenPastingIn k A B where
  isMoleculeIn_left := (isMoleculeIn_map_iff f A).1 h.isMoleculeIn_left
  isMoleculeIn_right := (isMoleculeIn_map_iff f B).1 h.isMoleculeIn_right
  inf_isSubmoleculeOf_left := by
    have h' := h.inf_isSubmoleculeOf_left
    rw [← map_inf, ← map_boundary] at h'
    exact (isSubmoleculeOf_map_iff f).1 h'
  inf_isSubmoleculeOf_right := by
    have h' := h.inf_isSubmoleculeOf_right
    rw [← map_inf, ← map_boundary] at h'
    exact (isSubmoleculeOf_map_iff f).1 h'
  boundary_isSubmoleculeOf_left := by
    have h' := h.boundary_isSubmoleculeOf_left
    rw [← map_sup, ← map_boundary, ← map_boundary] at h'
    exact (isSubmoleculeOf_map_iff f).1 h'
  boundary_isSubmoleculeOf_right := by
    have h' := h.boundary_isSubmoleculeOf_right
    rw [← map_sup, ← map_boundary, ← map_boundary] at h'
    exact (isSubmoleculeOf_map_iff f).1 h'

theorem IsPastingIn.isPastingAtIn_cond (β : Bool) {k : ℕ} {W U R : LowerSet P}
    (hW : IsMoleculeIn P W) (hU : IsMoleculeIn P U)
    (h : P.IsPastingIn k (cond β U W) (cond β W U) R) : P.IsPastingAtIn k β W U R := by
  cases β <;> simp only [cond_false, cond_true] at h
  · exact ⟨hW, hU, h.sup_eq.symm, h.inf_eq_output, by
      rw [h.inf_eq_input]; exact IsSubmoleculeOf.refl (hU.boundary k false)⟩
  · refine ⟨hW, hU, h.sup_eq.symm.trans (sup_comm _ _), ?_, ?_⟩
    · rw [inf_comm]; exact h.inf_eq_input
    · rw [inf_comm, h.inf_eq_output]; exact IsSubmoleculeOf.refl (hU.boundary k true)

end Atoms.Molecule.OGP

namespace Atoms.Diagrammatic

variable {X Y : DiagSet.{u}}

private theorem isDegenerate_cellAt_grayTensor {p : PastingDiagram X}
    (hp : p.IsDegenerate) (v : PastingDiagram Y) (t : (p.grayTensor v).shape.ogp)
    (ht : grade ℕ t = (p.grayTensor v).dim) :
    ∃ (U V : Atom) (g : diagram (Diagrammatic.grayTensor X Y) (Atom.grayTensor U V)),
      IsDegenerate (Diagrammatic.grayTensor X Y) g ∧
        (ofCell g).Equiv (ofCell ((p.grayTensor v).cellAt t)) := by
  obtain ⟨⟨s, r⟩, rfl⟩ : ∃ z, (p.shape.grayProductIso v.shape).hom z = t :=
    ⟨(p.shape.grayProductIso v.shape).inv t, by simp⟩
  have hg : grade ℕ (s, r) = p.dim + v.dim := by
    rw [← (isMorphism (p.shape.grayProductIso v.shape).hom).grade_eq, ht, dim_grayTensor]
  have hs : grade ℕ s ≤ p.dim := by
    have h := grade_le_krullDim s
    rw [p.shape.krullDim_eq_dimension] at h
    exact_mod_cast h
  have hr : grade ℕ r ≤ v.dim := by
    have h := grade_le_krullDim r
    rw [v.shape.krullDim_eq_dimension] at h
    exact_mod_cast h
  rw [Prod.grade_eq_add] at hg
  dsimp only at hg
  refine ⟨_, _, grayTensorCell (p.cellAt s) (v.cellAt r), isDegenerate_grayTensorCell
    (Or.inl (isDegenerate_cellAt_of_isDegenerate hp (by omega))), ?_⟩
  refine (grayTensor_ofCell _ _).symm.trans (Within.equiv_of_image_eq
    ((locatedCell p s).grayTensor (locatedCell v r)) (locatedCell _ _) ?_)
  have hc : ∀ {Z : DiagSet.{u}} (q : PastingDiagram Z) (x : q.shape.ogp),
      (locatedCell q x).image = LowerSet.Iic x := fun q x => image_principalEmb q x
  rw [Within.image_grayTensor, hc, hc, hc, ← map_Iic]
  exact congrArg _ (LowerSet.Iic_prod (s, r)).symm

theorem RoundPastingDiagram.grayTensor_mem_equivalences_of_isDegenerate
    {p : RoundPastingDiagram X} (hp : p.toPastingDiagram.IsDegenerate)
    (v : RoundPastingDiagram Y) : p.grayTensor v ∈ equivalences (Diagrammatic.grayTensor X Y) := by
  refine mem_equivalences_of_forall_cellAt _ (by
    change 0 < (p.toPastingDiagram.grayTensor v.toPastingDiagram).dim
    rw [PastingDiagram.dim_grayTensor]
    exact Nat.lt_add_right _ (PastingDiagram.dim_pos_of_isDegenerate hp)) fun t ht => ?_
  obtain ⟨U, V, g, hg, e⟩ := isDegenerate_cellAt_grayTensor hp v.toPastingDiagram t ht
  exact mem_equivalences_of_equiv e (mem_equivalences_of_isDegenerate (cellRound g)
    ((isDegenerate_ofCell_iff g).2 hg))

theorem RoundPastingDiagram.grayTensor_unit_mem_equivalences (b : RoundPastingDiagram X)
    (v : RoundPastingDiagram Y) :
    b.isRound.unit.grayTensor v ∈ equivalences (Diagrammatic.grayTensor X Y) :=
  grayTensor_mem_equivalences_of_isDegenerate (isDegenerate_unit _) v

noncomputable def grayTensorPoint (X : DiagSet.{u}) (y : diagram Y atomPoint) :
    X ⟶ Diagrammatic.grayTensor X Y :=
  (GrayDiagSet.rightUnitor X).inv ≫ grayTensorBifunctor.map (𝟙 X, uliftYonedaEquiv.symm y)

theorem grayTensorPoint_app (y : diagram Y atomPoint) {U : Atom} (x : diagram X U) :
    (grayTensorPoint X y).app (op U) x =
      (Diagrammatic.grayTensor X Y).map (Atom.grayTensorRightUnitor U).inv.op
        (grayTensorCell x y) := by
  have h₁ : (GrayDiagSet.rightUnitor X).inv.app (op U) x =
      (Diagrammatic.grayTensor X (ball atomPoint)).map (Atom.grayTensorRightUnitor U).inv.op
        (grayTensorCell x (uliftYonedaEquiv (𝟙 (ball.{u} atomPoint)))) := by
    have h : (GrayDiagSet.rightUnitor X).hom.app (op U)
        ((Diagrammatic.grayTensor X (ball atomPoint)).map (Atom.grayTensorRightUnitor U).inv.op
          (grayTensorCell x (uliftYonedaEquiv (𝟙 (ball.{u} atomPoint))))) = x := by
      rw [NatTrans.naturality_apply, GrayDiagSet.rightUnitor_hom_app_grayTensorCell,
        ← Functor.map_comp_apply, ← op_comp]
      have e : toAtomPoint atomPoint = 𝟙 atomPoint := isTerminalAtomPoint.hom_ext _ _
      rw [e, Atom.grayTensorMap_id, Category.id_comp, Iso.inv_hom_id, op_id,
        Functor.map_id_apply]
    conv_lhs => rw [← h]
    exact Iso.hom_inv_id_app_apply _ _ _
  rw [grayTensorPoint, NatTrans.comp_app_apply, h₁, NatTrans.naturality_apply,
    grayTensorCell_naturality]
  congr 2
  exact uliftYonedaEquiv.apply_symm_apply y

theorem PastingDiagram.grayTensor_ofCell_point_equiv (u : PastingDiagram X)
    (y : diagram Y atomPoint) :
    (u.grayTensor (ofCell y)).Equiv (u.mapTo (grayTensorPoint X y)) := by
  let φ : (u.shape.grayProduct (ofCell y).shape).ogp ≅ u.shape.ogp :=
    (u.shape.grayProductIso atomPoint.toMoleculeShape).symm ≪≫
      MonoidalCategory.whiskerLeftIso u.shape.ogp (FiniteOGP.ofOGPIso point).symm ≪≫
        grayProductRightUnitor u.shape.ogp
  refine ⟨φ, ?_⟩
  let E := realize.mapIso (RDCpx.isoOfIso (P := (u.shape.grayProduct (ofCell y).shape).rdc)
      (Q := grayProductRDC u.shape.rdc (ofCell y).shape.rdc)
      (u.shape.grayProductIso (ofCell y).shape).symm) ≪≫
    realizeGrayProductIso u.shape.rdc (ofCell y).shape.rdc
  rw [grayTensor_map]
  change _ = E.hom ≫ _
  rw [← Iso.inv_comp_eq]
  refine grayTensor_hom_ext fun U V f g => ?_
  let k : Atom.grayTensor U V ⟶ U :=
    Atom.grayTensorMap (𝟙 U) (toAtomPoint V) ≫ (Atom.grayTensorRightUnitor U).hom
  have hg : (ofCell y).map.app (op V) g = Y.map (toAtomPoint V).op y := by
    obtain ⟨g⟩ := g
    change atomToRDCpx.obj V ⟶ atomToRDCpx.obj atomPoint at g
    obtain rfl : g = atomToRDCpx.map (toAtomPoint V) := by
      ext t
      exact (MoleculeShape.subsingleton_of_dimension_eq_zero (P := atomPoint.toMoleculeShape)
        dimension_atomPoint).elim _ _
    exact ofCell_map_app_map y (toAtomPoint V)
  have hc : (E.inv ≫ realize.map (RDCpx.isoOfIso φ).hom).app _ (grayTensorCell f g) =
      (realize.obj u.shape.rdc).map k.op f := by
    obtain ⟨f⟩ := f
    obtain ⟨g⟩ := g
    change atomToRDCpx.obj U ⟶ u.shape.rdc at f
    change atomToRDCpx.obj V ⟶ atomToRDCpx.obj atomPoint at g
    simp only [E, Iso.trans_inv, Functor.mapIso_inv, Category.assoc, NatTrans.comp_app_apply,
      realizeGrayProductIso_inv_app_grayTensorCell]
    change ULift.up (grayProductCellMap f g ≫ (RDCpx.isoOfIso
      (P := (u.shape.grayProduct (ofCell y).shape).rdc) (Q := grayProductRDC u.shape.rdc
        (ofCell y).shape.rdc) (u.shape.grayProductIso (ofCell y).shape).symm).inv ≫
      (RDCpx.isoOfIso (P := (u.shape.grayProduct (ofCell y).shape).rdc) (Q := u.shape.rdc)
        φ).hom) = ULift.up (atomToRDCpx.map k ≫ f)
    congr 1
    ext t
    have h₁ (z : OGP.grayProduct u.shape.ogp atomPoint.toMoleculeShape.ogp) :
        φ.hom ((u.shape.grayProductIso atomPoint.toMoleculeShape).hom z) = z.1 := by
      change (grayProductRightUnitor u.shape.ogp).hom
        ((MonoidalCategory.whiskerLeftIso u.shape.ogp (FiniteOGP.ofOGPIso point).symm).hom
          ((u.shape.grayProductIso atomPoint.toMoleculeShape).inv
            ((u.shape.grayProductIso atomPoint.toMoleculeShape).hom z))) = z.1
      rw [Iso.hom_inv_id_apply]
      rfl
    change φ.hom ((u.shape.grayProductIso atomPoint.toMoleculeShape).hom
      ((grayProductCellMap f g).hom t)) = f.hom (k t)
    refine (h₁ _).trans ((congrArg Prod.fst (grayProductCellMap_apply f g t)).trans
      (congrArg f.hom ?_))
    simp [k]
  have hk : k ≫ (Atom.grayTensorRightUnitor U).inv = Atom.grayTensorMap (𝟙 U) (toAtomPoint V) := by
    simp only [k, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [grayTensorCell_naturality, hg, ← Category.assoc, NatTrans.comp_app_apply, hc]
  change (u.map ≫ grayTensorPoint X y).app _ _ = _
  rw [NatTrans.comp_app_apply, NatTrans.naturality_apply, NatTrans.naturality_apply,
    grayTensorPoint_app, ← Functor.map_comp_apply, ← op_comp, hk, ← grayTensorCell_restrict,
    op_id, Functor.map_id_apply]

theorem RoundPastingDiagram.grayTensor_mem_equivalences_of_dim_eq_zero {u : RoundPastingDiagram X}
    (hu : u ∈ equivalences X) {v : RoundPastingDiagram Y} (hv : v.dim = 0) :
    u.grayTensor v ∈ equivalences (Diagrammatic.grayTensor X Y) := by
  obtain ⟨y, e⟩ := PastingDiagram.exists_equiv_ofCell_of_dim_eq_zero hv
  refine mem_equivalences_of_equiv ?_ (mapTo_mem_equivalences (grayTensorPoint X y) hu)
  exact ((u.toPastingDiagram.grayTensor_ofCell_point_equiv y).symm.trans
    (Equiv.grayTensor (.refl _) e.symm))

theorem Staircase.hasSideInverse_inner (S : Staircase X) {A : Set (RoundPastingDiagram X)}
    (hM : S.ambient.IsRound) (hI : S.inner.IsRound)
    (hst : ∀ i, S.stage i (i + 1) =
      S.ambient.shape.ogp.boundary ⊤ (S.level + 1 + i) (S.sign i))
    (hsign : ∀ i, S.sign i = !S.side (i + 1))
    (h0 : ((Within.boundary S.inner S.level (!S.side 0)).trans S.innerWithin).image =
      S.ambient.shape.ogp.boundary ⊤ S.level (!S.side 0))
    {j : ℕ} (hjL : j < S.length) (hd : S.inner.dim = S.level + j + 1)
    (hxM : S.level + j ≤ S.ambient.dim) (hpos : 0 < S.level + j)
    (hA : ∀ i < j, S.piece i ∈ equivalences X) {v : RoundPastingDiagram X}
    (hv : HasSideInverse (PastingClosure A) (!S.side j) v)
    (huv : cond (S.side j)
      (ArrowIn (PastingClosure A)
        ⟨_, isRound_boundary_of_isRound hM (S.level + 1 + j) (S.sign j)⟩ v)
      (ArrowIn (PastingClosure A) v
        ⟨_, isRound_boundary_of_isRound hM (S.level + 1 + j) (S.sign j)⟩)) :
    HasSideInverse (PastingClosure A) (!S.side j) ⟨S.inner, hI⟩ := by
  have e : ((S.step j hjL).app ((S.ctx j).app S.inner)).Equiv
      (S.ambient.boundary (S.level + 1 + j) (S.sign j)) := by
    have h := S.app_ctx_succ_equiv_boundary hst j
    rw [S.ctx_succ hjL] at h
    exact (CtxExpr.app_equiv _ (equiv_boundary_dim S.inner (by omega) _).symm).trans h
  have hr : ((S.step j hjL).app ((S.ctx j).app S.inner)).IsRound :=
    e.isRound_iff.2 (isRound_boundary_of_isRound hM _ _)
  obtain ⟨α, hside⟩ : ∃ α, S.side j = α := ⟨_, rfl⟩
  rw [hside] at hv huv ⊢
  have huv' : cond α (ArrowIn (PastingClosure A) ⟨_, hr⟩ v)
      (ArrowIn (PastingClosure A) v ⟨_, hr⟩) := by
    cases α
    · exact ArrowIn.of_equiv_right huv e.symm
    · exact ArrowIn.of_equiv_left huv e.symm
  rcases j with _ | j
  · obtain ⟨k, hk⟩ : ∃ k, S.level = k + 1 := ⟨S.level - 1, by omega⟩
    have ha : IsRoundIn (S.inner.homAt k) (S.inner.boundary (k + 1) false) :=
      ⟨S.inner.inHom_homAt_boundary (by omega) (by omega) false, dim_boundary _ (by omega) _,
        isRound_boundary_of_isRound hI _ _⟩
    have hb : IsRoundIn (S.inner.homAt k) (S.inner.boundary (k + 1) true) :=
      ⟨S.inner.inHom_homAt_boundary (by omega) (by omega) true, dim_boundary _ (by omega) _,
        isRound_boundary_of_isRound hI _ _⟩
    have hu : IsRoundIn ⟨k + 1, S.inner.boundary (k + 1) false, S.inner.boundary (k + 1) true⟩
        S.inner := ⟨⟨by dsimp only; omega, .refl _, .refl _⟩, by dsimp only; omega, hI⟩
    obtain ⟨D, hT⟩ := S.exists_typed_step hjL (by omega)
    refine hasSideInverse_of_arrowIn_trim_comp (H := ha.roundHom) (H' := ha.roundHom) α
      (.id (.refl _)) ⟨.id (.refl _), isRoundCtx_id _⟩ ha hb (hT.congr_domain ⟨hk, ?_, ?_⟩) hside
      (u := ⟨S.inner, hI⟩) hu hr hv huv'
    · change (S.inner.boundary S.level false).Equiv (S.inner.boundary (k + 1) false)
      rw [hk]
    · change (S.inner.boundary S.level true).Equiv (S.inner.boundary (k + 1) true)
      rw [hk]
  · have ha : IsRoundIn (S.inner.homAt (S.level + j))
        (S.inner.boundary (S.level + (j + 1)) false) :=
      ⟨S.inner.inHom_homAt_boundary (by omega) (by omega) false, dim_boundary _ (by omega) _,
        isRound_boundary_of_isRound hI _ _⟩
    have hb : IsRoundIn (S.inner.homAt (S.level + j))
        (S.inner.boundary (S.level + (j + 1)) true) :=
      ⟨S.inner.inHom_homAt_boundary (by omega) (by omega) true, dim_boundary _ (by omega) _,
        isRound_boundary_of_isRound hI _ _⟩
    have ha' : IsRoundIn (S.ambient.homAt (S.level + j))
        (S.ambient.boundary (S.level + (j + 1)) false) :=
      ⟨S.ambient.inHom_homAt_boundary (by omega) hxM false, dim_boundary _ hxM _,
        isRound_boundary_of_isRound hM _ _⟩
    have hu : IsRoundIn ⟨S.level + j + 1, S.inner.boundary (S.level + (j + 1)) false,
        S.inner.boundary (S.level + (j + 1)) true⟩ S.inner :=
      ⟨⟨by dsimp only; omega, .refl _, .refl _⟩, by dsimp only; omega, hI⟩
    obtain ⟨D, hT⟩ := S.exists_typed_step hjL (by omega)
    exact hasSideInverse_of_arrowIn_trim_comp (H := ha.roundHom) (H' := ha'.roundHom) α
      (S.typed_ctx_homAt (fun i _ _ => hA i (by omega)) hst hsign h0 (by omega))
      ⟨S.typed_ctx_homAt (fun _ _ _ => trivial) hst hsign h0 (by omega),
        S.isRoundCtx_ctx hM hI hst (by omega)⟩ ha hb hT hside (u := ⟨S.inner, hI⟩) hu hr hv huv'

private theorem mem_equivalences_of_isGenPastingIn_within {M : PastingDiagram X}
    {m a b : RoundPastingDiagram X} {k : ℕ} (wm : Within m.toPastingDiagram M)
    (wa : Within a.toPastingDiagram M) (wb : Within b.toPastingDiagram M) (hda : a.dim = k + 1)
    (hdb : b.dim = k + 1) (hg : M.shape.ogp.IsGenPastingIn k wa.image wb.image)
    (hsup : wa.image ⊔ wb.image = wm.image)
    (iA : wa.image ⊓ M.shape.ogp.boundary wm.image k false ≤
      M.shape.ogp.boundary wa.image k false)
    (iB : wb.image ⊓ M.shape.ogp.boundary wm.image k true ≤
      M.shape.ogp.boundary wb.image k true)
    (ha : a ∈ equivalences X) (hb : b ∈ equivalences X) : m ∈ equivalences X := by
  have la : wa.image ≤ wm.image := hsup ▸ le_sup_left
  have lb : wb.image ≤ wm.image := hsup ▸ le_sup_right
  have ea : wa.image = OGP.map wm.emb (wa.ofImageLE wm la).image := by
    rw [← Within.image_trans, Within.image_ofImageLE_trans]
  have eb : wb.image = OGP.map wm.emb (wb.ofImageLE wm lb).image := by
    rw [← Within.image_trans, Within.image_ofImageLE_trans]
  have et : wm.image = OGP.map wm.emb ⊤ := rfl
  have refl_le {A B : LowerSet m.shape.ogp} (h : OGP.map wm.emb A ≤ OGP.map wm.emb B) : A ≤ B :=
    ((gc_map_comap wm.emb).le_iff_le.1 h).trans (comap_map wm.emb B).le
  refine mem_equivalences_of_isGenPastingIn (wa.ofImageLE wm la) (wb.ofImageLE wm lb) hda hdb
    ?_ ?_ ?_ ?_ ha hb
  · rw [ea, eb] at hg
    exact hg.of_map wm.emb
  · apply map_injective wm.emb
    rw [map_sup, ← ea, ← eb, hsup, et]
  · refine refl_le ?_
    rw [map_inf, map_boundary, map_boundary, ← ea, ← et]
    exact iA
  · refine refl_le ?_
    rw [map_inf, map_boundary, map_boundary, ← eb, ← et]
    exact iB

private theorem inf_boundary_boundary_grayProduct_le {P Q : MoleculeShape} {Xp : LowerSet P.ogp}
    {Yp : LowerSet Q.ogp} (hX : P.ogp.IsSubmoleculeOf Xp ⊤) (hY : Q.ogp.IsSubmoleculeOf Yp ⊤)
    {N : ℕ} (hN : 0 < N) (γ δ : Bool) :
    OGP.map (P.grayProductIso Q).hom ((grayProduct _ _).boundary (Xp ×ˢ Yp) N γ) ⊓
        (P.grayProduct Q).ogp.boundary ((P.grayProduct Q).ogp.boundary ⊤ N γ) (N - 1) δ ≤
      (P.grayProduct Q).ogp.boundary
        (OGP.map (P.grayProductIso Q).hom ((grayProduct _ _).boundary (Xp ×ˢ Yp) N γ))
        (N - 1) δ := by
  rw [← map_top_of_isIso (P.grayProductIso Q).hom, ← LowerSet.top_prod_top, ← map_boundary,
    ← map_boundary, ← map_inf, ← map_boundary]
  refine map_mono _ ?_
  rw [isGlobular_prod P.isMolecule.isGlobular Q.isMolecule.isGlobular (N - 1) N (by omega) δ γ]
  exact inf_boundary_boundary_prod_le P.isMolecule Q.isMolecule hX hY (by omega) γ δ

theorem RoundPastingDiagram.boundary_grayTensor_mem_equivalences {h : RoundPastingDiagram X}
    {v : RoundPastingDiagram Y} {n ℓ : ℕ} (hh : h.dim = n + 1) (hv : v.dim = ℓ + 1) (γ : Bool)
    (h₁ : (⟨h.boundary n γ, isRound_boundary_of_isRound h.isRound n γ⟩ :
      RoundPastingDiagram X).grayTensor v ∈ equivalences (Diagrammatic.grayTensor X Y))
    (h₂ : ∀ v' : RoundPastingDiagram Y, v'.dim = ℓ →
      h.grayTensor v' ∈ equivalences (Diagrammatic.grayTensor X Y)) :
    (⟨(h.grayTensor v).boundary (n + ℓ + 1) γ,
        isRound_boundary_of_isRound (h.grayTensor v).isRound _ _⟩ :
      RoundPastingDiagram (Diagrammatic.grayTensor X Y)) ∈
      equivalences (Diagrammatic.grayTensor X Y) := by
  have hd₁ : ((h.boundary n γ).grayTensor v.toPastingDiagram).dim = n + ℓ + 1 := by
    rw [PastingDiagram.dim_grayTensor, dim_boundary _ (by omega)]
    omega
  have hd₂ : (h.toPastingDiagram.grayTensor (v.boundary (n + ℓ + 1 - n - 1)
      (xor (n + 1).bodd γ))).dim = n + ℓ + 1 := by
    rw [PastingDiagram.dim_grayTensor, dim_boundary _ (by omega)]
    omega
  let p₁ : RoundPastingDiagram (Diagrammatic.grayTensor X Y) :=
    ⟨((h.boundary n γ).grayTensor v.toPastingDiagram).boundary (n + ℓ + 1) γ,
      isRound_boundary_of_isRound (isRound_grayTensor (isRound_boundary_of_isRound h.isRound _ _)
        v.isRound) _ _⟩
  let v₂ : RoundPastingDiagram Y :=
    ⟨v.boundary (n + ℓ + 1 - n - 1) (xor (n + 1).bodd γ), isRound_boundary_of_isRound v.isRound _ _⟩
  let p₂ : RoundPastingDiagram (Diagrammatic.grayTensor X Y) :=
    ⟨(h.toPastingDiagram.grayTensor v₂.toPastingDiagram).boundary (n + ℓ + 1) γ,
      isRound_boundary_of_isRound (isRound_grayTensor h.isRound v₂.isRound) _ _⟩
  have hp₁ : p₁ ∈ equivalences _ :=
    mem_equivalences_of_equiv (equiv_boundary_dim _ hd₁.le γ).symm h₁
  have hp₂ : p₂ ∈ equivalences _ :=
    mem_equivalences_of_equiv (equiv_boundary_dim _ hd₂.le γ).symm
      (h₂ v₂ (by change (v.boundary _ _).dim = ℓ; rw [dim_boundary _ (by omega)]; omega))
  have hdp₁ : p₁.dim = n + ℓ + 1 := dim_boundary _ hd₁.ge _
  have hdp₂ : p₂.dim = n + ℓ + 1 := dim_boundary _ hd₂.ge _
  have hj : n < n + ℓ + 1 := by omega
  have hg := Within.isGenPastingIn_boundarySplit h.toPastingDiagram v.toPastingDiagram hj γ
  rw [show n + ℓ + 1 - 1 = n + ℓ by omega] at hg
  have hsup := Within.image_boundarySplitFst_sup h.toPastingDiagram v.toPastingDiagram hj γ
  have i₁ (δ : Bool) := inf_boundary_boundary_grayProduct_le
    (h.shape.isMolecule.boundary_isSubmoleculeOf n γ) (IsSubmoleculeOf.refl v.shape.isMolecule)
    (N := n + ℓ + 1) (by omega) γ δ
  have i₂ (δ : Bool) := inf_boundary_boundary_grayProduct_le
    (IsSubmoleculeOf.refl h.shape.isMolecule)
    (v.shape.isMolecule.boundary_isSubmoleculeOf (n + ℓ + 1 - n - 1) (xor (n + 1).bodd γ))
    (N := n + ℓ + 1) (by omega) γ δ
  rw [← Within.image_boundarySplitFst, Nat.add_sub_cancel] at i₁
  rw [← Within.image_boundarySplitSnd, Nat.add_sub_cancel] at i₂
  cases γ
  · refine mem_equivalences_of_isGenPastingIn_within (Within.boundary _ _ false) (a := p₁)
      (b := p₂) (Within.boundarySplitFst _ _ _ _ _) (Within.boundarySplitSnd _ _ _ _ _) hdp₁ hdp₂
      hg hsup ?_ ?_ hp₁ hp₂
    · rw [Within.image_boundary]; exact i₁ false
    · rw [Within.image_boundary]; exact i₂ true
  · refine mem_equivalences_of_isGenPastingIn_within (Within.boundary _ _ true) (a := p₂)
      (b := p₁) (Within.boundarySplitSnd _ _ _ _ _) (Within.boundarySplitFst _ _ _ _ _) hdp₂ hdp₁
      hg ((sup_comm _ _).trans hsup) ?_ ?_ hp₂ hp₁
    · rw [Within.image_boundary]; exact i₂ false
    · rw [Within.image_boundary]; exact i₁ true

private theorem arrowIn_boundary {S : Set (RoundPastingDiagram X)} {x : RoundPastingDiagram X}
    (hx : x ∈ S) {N : ℕ} (hN : x.dim = N + 1) :
    ArrowIn S ⟨x.boundary N false, isRound_boundary_of_isRound x.isRound N false⟩
      ⟨x.boundary N true, isRound_boundary_of_isRound x.isRound N true⟩ :=
  have hle : N ≤ x.toPastingDiagram.dim := by omega
  ⟨x, hx, HasBdry.of_dim_eq (dim_boundary x.toPastingDiagram hle false).symm hN rfl
    ((dim_boundary x.toPastingDiagram hle true).trans
      (dim_boundary x.toPastingDiagram hle false).symm)
    (.refl _) (.refl _)⟩

private theorem cond_arrowIn_of_equiv (A : Set (RoundPastingDiagram X)) (s : Bool)
    {a b : RoundPastingDiagram X} (e : a.Equiv b.toPastingDiagram) :
    cond s (ArrowIn (PastingClosure A) a b) (ArrowIn (PastingClosure A) b a) := by
  cases s
  · exact (arrowIn_pastingClosure_refl A b).of_equiv_right e.symm
  · exact (arrowIn_pastingClosure_refl A a).of_equiv_right e

private theorem hasSideInverse_grayTensor_step {ℓ : ℕ}
    (IH : ∀ u ∈ equivalences X, ∀ v' : RoundPastingDiagram Y, v'.dim < ℓ + 1 →
      u.grayTensor v' ∈ equivalences (Diagrammatic.grayTensor X Y))
    {e : RoundPastingDiagram X} (he : e ∈ equivalences X) {v : RoundPastingDiagram Y}
    (hv : v.dim = ℓ + 1) (β : Bool) :
    HasSideInverse (PastingClosure {x | ∃ u ∈ equivalences X, x = u.grayTensor v}) β
      (e.grayTensor v) := by
  let A : Set (RoundPastingDiagram (Diagrammatic.grayTensor X Y)) :=
    {x | ∃ u ∈ equivalences X, x = u.grayTensor v}
  have hA {u : RoundPastingDiagram X} (hu : u ∈ equivalences X) :
      u.grayTensor v ∈ PastingClosure A :=
    subset_pastingClosure A ⟨u, hu, rfl⟩
  have D := ((mem_equivalences_iff e).1 he).data
  have hpos := D.dim_pos
  have hpiece (w : RoundPastingDiagram X) (hw : w ∈ equivalences X) (i : ℕ) (hi : i < ℓ + 1)
      (γ : Bool) : w.grayTensor ⟨v.boundary i γ, isRound_boundary_of_isRound v.isRound _ _⟩ ∈
        equivalences (Diagrammatic.grayTensor X Y) :=
    IH w hw _ (by change (v.boundary i γ).dim < _; rw [dim_boundary _ (by omega)]; omega)
  have hh : D.invertor β ∈ equivalences X := D.invertor_mem β
  have hdh : (D.invertor β).dim = e.dim + 1 := D.dim_invertor β
  let S₁ := Within.grayStaircase (Within.refl (D.invertor β).toPastingDiagram)
    (Within.boundary (D.invertor β).toPastingDiagram e.dim (!(!β)))
    (isPastingAtIn_refl_boundary (D.invertor β).toPastingDiagram e.dim (!β)) hdh v
  have hI₁ : S₁.inner.IsRound := isRound_grayTensor (isRound_boundary_of_isRound
    (D.invertor β).isRound _ _) v.isRound
  have hM₁ : S₁.ambient.IsRound := isRound_grayTensor (D.invertor β).isRound v.isRound
  have hu₁ : (⟨(D.invertor β).boundary e.dim (!β), isRound_boundary_of_isRound
      (D.invertor β).isRound _ _⟩ : RoundPastingDiagram X).grayTensor v ∈
        equivalences (Diagrammatic.grayTensor X Y) :=
    mem_equivalences_of_equiv
      (e := (isRound_boundary_of_isRound e.isRound (e.dim - 1) β).unit.grayTensor v)
      (Equiv.grayTensor (D.boundary_invertor_unit β).symm (.refl v.toPastingDiagram))
      (RoundPastingDiagram.grayTensor_unit_mem_equivalences
        ⟨_, isRound_boundary_of_isRound e.isRound _ _⟩ v)
  have hb₁ := RoundPastingDiagram.boundary_grayTensor_mem_equivalences hdh hv (!β) hu₁
    (fun v' hv' => IH _ hh v' (by omega))
  have hN : e.dim + ℓ + 1 = S₁.level + 1 + ℓ := by
    change _ = e.dim + 1 + ℓ; omega
  have r₁ := S₁.hasSideInverse_inner (A := A)
    hM₁ hI₁ (Within.stage_succ_self_grayStaircase _ _ _ _ _)
    (Within.sign_grayStaircase _ _ _ _ _) (Within.image_boundary_level_grayStaircase _ _ _ _ _)
    (j := ℓ) (by change ℓ < v.dim + 1; omega)
    (by
      change ((D.invertor β).boundary e.dim (!(!β)) |>.grayTensor v.toPastingDiagram).dim = _
      rw [PastingDiagram.dim_grayTensor, dim_boundary _ (by omega)]
      change _ = e.dim + ℓ + 1; omega)
    (by
      change e.dim + ℓ ≤ ((D.invertor β).toPastingDiagram.grayTensor v.toPastingDiagram).dim
      rw [PastingDiagram.dim_grayTensor]; omega)
    (by change 0 < e.dim + ℓ; omega)
    (fun i hi => hpiece _ hh i (by omega) _)
    (hasSideInverse_of_mem_equivalences _ _ hb₁)
    (by
      have hx : ((D.invertor β).toPastingDiagram.grayTensor v.toPastingDiagram).dim =
          S₁.level + 1 + ℓ + 1 := by
        rw [PastingDiagram.dim_grayTensor]; change (D.invertor β).dim + v.dim = e.dim + 1 + ℓ + 1
        omega
      have ar := arrowIn_boundary (hA hh) hx
      have e₁ (γ : Bool) : (((D.invertor β).toPastingDiagram.grayTensor
          v.toPastingDiagram).boundary (S₁.level + 1 + ℓ) γ).Equiv
            (((D.invertor β).toPastingDiagram.grayTensor v.toPastingDiagram).boundary
              (e.dim + ℓ + 1) γ) := by
        rw [hN]
      cases β
      · exact ar.of_equiv_right (e₁ true)
      · exact ar.of_equiv_left (e₁ false))
  have hp : (cond (!β) e.toPastingDiagram (D.inverse β).toPastingDiagram).Pastable
      (cond (!β) (D.inverse β).toPastingDiagram e.toPastingDiagram) (e.dim - 1) := by
    cases β
    · exact D.pastable false
    · exact D.pastable true
  have hcomp : ((D.invertor β).boundary e.dim β).Equiv
      ((cond (!β) e.toPastingDiagram (D.inverse β).toPastingDiagram).paste
        (cond (!β) (D.inverse β).toPastingDiagram e.toPastingDiagram) (e.dim - 1) hp) := by
    cases β
    · exact D.boundary_invertor_composite false
    · exact D.boundary_invertor_composite true
  have hinv : D.inverse β ∈ equivalences X := by
    cases β
    · exact D.leftInverse_mem he
    · exact D.rightInverse_mem he
  obtain ⟨wc, hpst⟩ := Within.exists_isPastingIn_pasteIn (!β) hp
  have hc := hpst.isPastingAtIn_cond (!β) (Within.isMoleculeIn_image _)
    (Within.isMoleculeIn_image _)
  have hw₂ : (D.inverse β).dim = e.dim - 1 + 1 := by rw [D.dim_inverse]; omega
  let S₂ := Within.grayStaircase (Within.pasteIn (!β) hp) wc hc hw₂ v
  have hdc := (dim_eq_of_equiv hcomp).symm.trans
    (dim_boundary (D.invertor β).toPastingDiagram (by omega) β)
  have hM₂ : S₂.ambient.IsRound := isRound_grayTensor
    (hcomp.isRound_iff.1 (isRound_boundary_of_isRound (D.invertor β).isRound _ _)) v.isRound
  have hI₂ : S₂.inner.IsRound := isRound_grayTensor e.isRound v.isRound
  have hd₂ : S₂.ambient.dim = S₂.level + 1 + (ℓ + 1) := by
    change (PastingDiagram.grayTensor _ v.toPastingDiagram).dim = e.dim - 1 + 1 + (ℓ + 1)
    rw [PastingDiagram.dim_grayTensor, hdc]; omega
  have eB : (S₂.ambient.boundary (S₂.level + 1 + (ℓ + 1)) (S₂.sign (ℓ + 1))).Equiv S₁.inner := by
    refine (equiv_boundary_dim _ hd₂.le _).trans ((Equiv.grayTensor hcomp.symm
      (.refl v.toPastingDiagram)).trans ?_)
    change (((D.invertor β).boundary e.dim β).grayTensor v.toPastingDiagram).Equiv
      (((D.invertor β).boundary e.dim (!(!β))).grayTensor v.toPastingDiagram)
    rw [Bool.not_not]
  have r₂ := S₂.hasSideInverse_inner (A := A) hM₂ hI₂
    (Within.stage_succ_self_grayStaircase _ _ _ _ _)
    (Within.sign_grayStaircase _ _ _ _ _) (Within.image_boundary_level_grayStaircase _ _ _ _ _)
    (j := ℓ + 1) (by change ℓ + 1 < v.dim + 1; omega)
    (by
      change (e.toPastingDiagram.grayTensor v.toPastingDiagram).dim = e.dim - 1 + (ℓ + 1) + 1
      rw [PastingDiagram.dim_grayTensor]; omega)
    (by omega) (by change 0 < e.dim - 1 + (ℓ + 1); omega)
    (fun i hi => hpiece _ hinv i hi _) (v := ⟨S₁.inner, hI₁⟩) r₁
    (cond_arrowIn_of_equiv A _ eB)
  have hs : S₂.side (ℓ + 1) = !β := rfl
  rw [hs, Bool.not_not] at r₂
  exact r₂

theorem RoundPastingDiagram.grayTensor_mem_equivalences_left {u : RoundPastingDiagram X}
    (hu : u ∈ equivalences X) (v : RoundPastingDiagram Y) :
    u.grayTensor v ∈ equivalences (Diagrammatic.grayTensor X Y) := by
  induction hℓ : v.dim using Nat.strong_induction_on generalizing u v with
  | _ ℓ IH =>
    rcases ℓ with _ | ℓ
    · exact grayTensor_mem_equivalences_of_dim_eq_zero hu hℓ
    · have IH' : ∀ u ∈ equivalences X, ∀ v' : RoundPastingDiagram Y, v'.dim < ℓ + 1 →
          u.grayTensor v' ∈ equivalences (Diagrammatic.grayTensor X Y) :=
        fun u hu v' hv' => IH _ hv' hu v' rfl
      have hA : {x | ∃ u ∈ equivalences X, x = u.grayTensor v} ⊆
          biInvOperator _ (PastingClosure {x | ∃ u ∈ equivalences X, x = u.grayTensor v}) := by
        rintro _ ⟨u', hu', rfl⟩
        exact mem_biInvOperator_iff.2 ⟨hasSideInverse_grayTensor_step IH' hu' hℓ false,
          hasSideInverse_grayTensor_step IH' hu' hℓ true⟩
      exact pastingClosure_subset_equivalences hA (subset_pastingClosure _ ⟨u, hu, rfl⟩)

end Atoms.Diagrammatic
