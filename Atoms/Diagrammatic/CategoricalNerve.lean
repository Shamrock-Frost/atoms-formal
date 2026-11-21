import Atoms.Diagrammatic.OneTruncation
import Atoms.Diagrammatic.Core
import Atoms.Diagrammatic.BicategoryNerve.InftyTwo

open CategoryTheory Simplicial Opposite
open Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe v u

namespace Atoms.Diagrammatic

variable {X Y Z : DiagSet.{u}}

open scoped SimplicialSeedQuotient

local macro "trmap[" f:term "]" : term =>
  `((SSet.truncation 2).map (DiagSet.toSSet.map $f))

namespace SimplicialSeedQuotient

private theorem hmap_comp (f : X ⟶ Y) (g : Y ⟶ Z) : hmap[f ≫ g] = hmap[f] ⋙ hmap[g] :=
  congrArg Cat.Hom.toFunctor ((DiagSet.toSSet ⋙ SSet.hoFunctor).map_comp f g)

section Bijective

variable {A B : DiagSet.{u}} (ι : A ⟶ B)

private theorem isIso_trmap (h : ∀ V : Atom, V.dimension ≤ 2 → Function.Bijective (ι.app (op V))) :
    IsIso trmap[ι] := by
  have (n : (SimplexCategory.Truncated 2)ᵒᵖ) : IsIso (trmap[ι].app n) :=
    (isIso_iff_bijective _).2 (h (atomSimplex n.unop.obj.len)
      ((dimension_atomSimplex _).trans_le n.unop.property))
  exact NatIso.isIso_of_isIso_app _

variable (h : ∀ V : Atom, V.dimension ≤ 2 → Function.Bijective (ι.app (op V)))

private noncomputable def hinv :
    SSet.Truncated.HomotopyCategory tr₂[B] ⥤ SSet.Truncated.HomotopyCategory tr₂[A] :=
  haveI := isIso_trmap ι h
  SSet.Truncated.mapHomotopyCategory (inv trmap[ι])

private theorem hmap_comp_hinv : hmap[ι] ⋙ hinv ι h = 𝟭 _ :=
  haveI := isIso_trmap ι h
  (congrArg Cat.Hom.toFunctor
    (SSet.Truncated.hoFunctor₂.map_comp trmap[ι] (inv trmap[ι]))).symm.trans
    (by rw [IsIso.hom_inv_id, SSet.Truncated.hoFunctor₂.map_id]; rfl)

private theorem hinv_comp_hmap : hinv ι h ⋙ hmap[ι] = 𝟭 _ :=
  haveI := isIso_trmap ι h
  (congrArg Cat.Hom.toFunctor
    (SSet.Truncated.hoFunctor₂.map_comp (inv trmap[ι]) trmap[ι])).symm.trans
    (by rw [IsIso.inv_hom_id, SSet.Truncated.hoFunctor₂.map_id]; rfl)

private theorem hinv_map_eq_of_rel {a b : SSet.Truncated.HomotopyCategory tr₂[B]} (φ ψ : a ⟶ b)
    (hr : Rel B φ ψ) :
    (hinv ι h ⋙ quotientFunctor A).map φ = (hinv ι h ⋙ quotientFunctor A).map ψ := by
  induction hr with
  | @boundary V hV c x y φ ψ hφ hψ =>
    obtain ⟨c', rfl⟩ := (h V hV.le).2 c
    have hk : hmap[uliftYonedaEquiv.symm (ι.app _ c')] ⋙ hinv ι h =
        hmap[uliftYonedaEquiv.symm c'] := by
      rw [← uliftYonedaEquiv_symm_comp, hmap_comp, Functor.assoc, hmap_comp_hinv, Functor.comp_id]
    have e := CategoryTheory.Quotient.sound _ (Rel.boundary hV c' hφ hψ)
    change (quotientFunctor A).map
        ((hmap[uliftYonedaEquiv.symm (ι.app _ c')] ⋙ hinv ι h).map φ) =
      (quotientFunctor A).map
        ((hmap[uliftYonedaEquiv.symm (ι.app _ c')] ⋙ hinv ι h).map ψ)
    rw [Functor.congr_hom hk, Functor.congr_hom hk, Functor.map_comp, Functor.map_comp,
      Functor.map_comp, Functor.map_comp]
    exact congrArg (_ ≫ · ≫ _) e

private noncomputable def mapInv : SimplicialSeedQuotient B ⥤ SimplicialSeedQuotient A :=
  lift (hinv ι h ⋙ quotientFunctor A) fun _ _ => hinv_map_eq_of_rel ι h

private theorem map_comp_mapInv : map ι ⋙ mapInv ι h = 𝟭 _ := by
  refine CategoryTheory.Quotient.lift_unique' _ _ _ ?_
  exact (congrArg (· ⋙ mapInv ι h) (quotientFunctor_comp_map ι)).trans
    ((congrArg (hmap[ι] ⋙ ·) (quotientFunctor_comp_lift _ fun _ _ =>
      hinv_map_eq_of_rel ι h)).trans
      (congrArg (· ⋙ quotientFunctor A) (hmap_comp_hinv ι h)))

private theorem mapInv_comp_map : mapInv ι h ⋙ map ι = 𝟭 _ := by
  refine CategoryTheory.Quotient.lift_unique' _ _ _ ?_
  exact (congrArg (· ⋙ map ι)
    (quotientFunctor_comp_lift _ fun _ _ => hinv_map_eq_of_rel ι h)).trans
    ((congrArg (hinv ι h ⋙ ·) (quotientFunctor_comp_map ι)).trans
      (congrArg (· ⋙ quotientFunctor B) (hinv_comp_hmap ι h)))

end Bijective

end SimplicialSeedQuotient

open SimplicialSeedQuotient in
theorem isIso_oneTruncation_map_of_bijective {A B : DiagSet.{u}} (ι : A ⟶ B)
    (h : ∀ V : Atom, V.dimension ≤ 2 → Function.Bijective (ι.app (op V))) :
    IsIso (oneTruncation.map ι) := by
  refine ⟨(ofOneTruncation B ⋙ mapInv ι h ⋙ toOneTruncation A).toCatHom, Cat.Hom.ext ?_,
    Cat.Hom.ext ?_⟩
  · exact (congrArg (· ⋙ mapInv ι h ⋙ toOneTruncation A) (ofOneTruncation_naturality ι)).trans
      ((congrArg (fun H => ofOneTruncation A ⋙ H ⋙ toOneTruncation A) (map_comp_mapInv ι h)).trans
        (ofOneTruncation_comp_toOneTruncation A))
  · exact (congrArg ((ofOneTruncation B ⋙ mapInv ι h) ⋙ ·)
      (toOneTruncation_naturality ι).symm).trans
      ((congrArg (fun H => ofOneTruncation B ⋙ H ⋙ toOneTruncation B) (mapInv_comp_map ι h)).trans
        (ofOneTruncation_comp_toOneTruncation B))

open Atoms.Molecule Atoms.Molecule.OGP in
theorem bijective_realize_map_restrictIncl_app (W : Atom) {V : Atom}
    (hV : V.dimension < W.dimension) :
    Function.Bijective
      ((realize.{u}.map (W.rdc.restrictIncl (W.ogp.bdryFull ⊤))).app (op V)) := by
  refine ⟨?_, ?_⟩
  · have := mono_realize_map.{u} (W.rdc.restrictIncl (W.ogp.bdryFull ⊤)) Subtype.val_injective
    exact (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 this (op V))
  · rintro ⟨f⟩
    have hf : ∀ x, ConcreteCategory.hom f.hom x ∈ W.ogp.bdryFull ⊤ := fun x => by
      rw [Atom.mem_bdryFull_top_iff]
      intro hx
      have h₁ : grade ℕ (ConcreteCategory.hom f.hom x) ≤ grade ℕ x :=
        (ConcreteCategory.hom f.hom).isMap.grade_le x
      have h₂ := V.grade_le_dimension x
      rw [hx, ← W.dimension_eq] at h₁
      omega
    exact ⟨⟨RDCpx.codRestrict f _ hf⟩, congrArg ULift.up (RDCpx.codRestrict_restrictIncl f _ hf)⟩

theorem Parallel.exists_categoricalNerve_filler {C : Cat.{u, u}}
    {s t : RoundPastingDiagram (categoricalNerve.obj C)} (h : Parallel s t) (hs : 2 ≤ s.dim) :
    ∃ x : diagram (categoricalNerve.obj C) h.cellShape,
      HasRoundType (PastingDiagram.ofCell x) s t := by
  let i := realize.{u}.map (h.cellShape.rdc.restrictIncl (h.cellShape.ogp.bdryFull ⊤))
  have : IsIso (oneTruncation.map i) := isIso_oneTruncation_map_of_bijective i fun V hV =>
    bijective_realize_map_restrictIncl_app h.cellShape (by rw [h.dimension_cellShape]; omega)
  let g : realize.obj h.cellShape.rdc ⟶ categoricalNerve.obj C :=
    oneTruncationAdjunction.homEquiv _ _
      (inv (oneTruncation.map i) ≫ (oneTruncationAdjunction.homEquiv _ _).symm h.sphere)
  have hg : i ≫ g = h.sphere := by
    rw [← Adjunction.homEquiv_naturality_left, IsIso.hom_inv_id_assoc, Equiv.apply_symm_apply]
  refine ⟨uliftYonedaEquiv ((realizeAtomIso h.cellShape).inv ≫ g), ?_⟩
  have hx := (h.hasRoundType_ofCell_iff (𝟙 _)
    (uliftYonedaEquiv ((realizeAtomIso h.cellShape).inv ≫ g))).2 (by
      rw [Category.comp_id, ← hg]
      congr 1
      change (realizeAtomIso h.cellShape).hom ≫ uliftYonedaEquiv.symm _ = g
      rw [Equiv.symm_apply_apply, Iso.hom_inv_id_assoc])
  rwa [RoundPastingDiagram.mapTo_id, RoundPastingDiagram.mapTo_id] at hx

open Atoms.Molecule Atoms.Molecule.OGP in
private theorem realize_cell_cases (W : Atom) {V : Atom} (hV : V.dimension = W.dimension)
    (c : diagram (realize.{u}.obj W.rdc) V) :
    (∃ c', (realize.{u}.map (W.rdc.restrictIncl (W.ogp.bdryFull ⊤))).app (op V) c' = c) ∨
      (ofCell c).Equiv (ofCell (⟨𝟙 _⟩ : diagram (realize.{u}.obj W.rdc) W)) := by
  rcases c with ⟨f⟩
  by_cases hf : ∀ x, ConcreteCategory.hom f.hom x ∈ W.ogp.bdryFull ⊤
  · exact Or.inl ⟨⟨RDCpx.codRestrict f _ hf⟩,
      congrArg ULift.up (RDCpx.codRestrict_restrictIncl f _ hf)⟩
  · right
    push Not at hf
    obtain ⟨x, hx⟩ := hf
    rw [Atom.mem_bdryFull_top_iff, not_not] at hx
    let g : V ⟶ W := Atom.fullyFaithful.preimage f
    have hg : IsCollapseHom g := fun y => by
      have hy : y ∈ Set.Iic (g V.top) := by
        refine (W.le_top y).trans (hx.symm.trans_le ?_)
        exact (Atom.isMap g).monotone (V.le_top x)
      obtain ⟨z, -, hz⟩ := ((Atom.isMap g).image_Iic V.top).symm ▸ hy
      exact ⟨z, hz⟩
    have := isIso_of_isCollapseHom_of_dimension_eq g hg hV
    have hc : (⟨f⟩ : diagram (realize.{u}.obj W.rdc) V) =
        (realize.{u}.obj W.rdc).map (asIso g).hom.op ⟨𝟙 _⟩ :=
      congrArg ULift.up ((Atom.fullyFaithful.map_preimage f).symm.trans (Category.comp_id _).symm)
    rw [hc]
    exact equiv_ofCell_map_iso (asIso g) _

local macro "sph[" W:term "]" : term =>
  `(realize.obj (($W).rdc.restrict (($W).ogp.bdryFull ⊤)))

local macro "incl[" W:term "]" : term =>
  `(realize.map (($W).rdc.restrictIncl (($W).ogp.bdryFull ⊤)))

section Two

variable (W : Atom) (hW : W.dimension = 2)

private noncomputable def cellEquiv {V : Atom} (hV : V.dimension < 2) :
    diagram (sph[W] : DiagSet.{u}) V ≃ diagram (realize.{u}.obj W.rdc) V :=
  Equiv.ofBijective _ (bijective_realize_map_restrictIncl_app W (by rw [hW]; exact hV))

private noncomputable def vertexEquiv :
    (sph[W] : DiagSet.{u}).Vertex ≃ (realize.{u}.obj W.rdc).Vertex :=
  cellEquiv W hW (V := atomPoint) (by rw [dimension_atomPoint]; omega)

private noncomputable def globeEquiv :
    diagram (sph[W] : DiagSet.{u}) (atomGlobe 1) ≃ diagram (realize.{u}.obj W.rdc) (atomGlobe 1) :=
  cellEquiv W hW (V := atomGlobe 1) (by rw [dimension_atomGlobe]; omega)

private noncomputable def edgeBack {r r' : (realize.{u}.obj W.rdc).Vertex}
    (ε : (realize.{u}.obj W.rdc).Edge r r') :
    (sph[W] : DiagSet.{u}).Edge ((vertexEquiv W hW).symm r) ((vertexEquiv W hW).symm r') where
  cell := (globeEquiv W hW).symm ε.cell
  src_eq := (vertexEquiv W hW).injective
    ((NatTrans.naturality_apply incl[W] (atomGlobeVertex false).op _).trans
      ((congrArg ((realize.{u}.obj W.rdc).map (atomGlobeVertex false).op)
        (Equiv.apply_symm_apply (globeEquiv W hW) ε.cell)).trans
          (ε.src_eq.trans (Equiv.apply_symm_apply (vertexEquiv W hW) r).symm)))
  tgt_eq := (vertexEquiv W hW).injective
    ((NatTrans.naturality_apply incl[W] (atomGlobeVertex true).op _).trans
      ((congrArg ((realize.{u}.obj W.rdc).map (atomGlobeVertex true).op)
        (Equiv.apply_symm_apply (globeEquiv W hW) ε.cell)).trans
          (ε.tgt_eq.trans (Equiv.apply_symm_apply (vertexEquiv W hW) r').symm)))

private theorem ofCell_taut_map :
    (ofCell (⟨𝟙 _⟩ : diagram (realize.{u}.obj W.rdc) W)).map = 𝟙 (realize.obj W.rdc) := by
  ext ⟨T⟩ ⟨c⟩
  rfl

end Two

section Extension

variable (W : Atom) (hW : W.dimension = 2) {D : Type*} [Category* D]
  (F : OneTruncation (sph[W] : DiagSet.{u}) ⥤ D) (a b : RoundPastingDiagram (sph[W] : DiagSet.{u}))
  (ha : ((ofCell (⟨𝟙 _⟩ : diagram (realize.{u}.obj W.rdc) W)).boundary 1 false).Equiv
    (a.toPastingDiagram.mapTo incl[W]))
  (hb : ((ofCell (⟨𝟙 _⟩ : diagram (realize.{u}.obj W.rdc) W)).boundary 1 true).Equiv
    (b.toPastingDiagram.mapTo incl[W]))
  (hF : ∀ {x y x' y' : (sph[W] : DiagSet.{u}).Vertex} {p : OneTruncation.point x ⟶
      OneTruncation.point y} {p' : OneTruncation.point x' ⟶ OneTruncation.point y'},
    IsComposite a.toPastingDiagram p → IsComposite b.toPastingDiagram p' →
      Arrow.mk (F.map ((OneTruncation.quotientFunctor _).map p)) =
        Arrow.mk (F.map ((OneTruncation.quotientFunctor _).map p')))

private noncomputable def extInterpretation :
    OneTruncation.Interpretation (realize.{u}.obj W.rdc) D where
  obj r := F.obj (OneTruncation.mk ((vertexEquiv W hW).symm r))
  map ε := F.map (OneTruncation.globeHomMk (edgeBack W hW ε))

private theorem freeMap_comp_extFreeLift :
    OneTruncation.freeMap incl[W] ⋙ (extInterpretation W hW F).freeLift =
      OneTruncation.quotientFunctor _ ⋙ F :=
  OneTruncation.Free.functor_ext fun _ _ t =>
    (congrArg Arrow.mk ((congrArg (extInterpretation W hW F).freeLift.map
      (OneTruncation.freeMap_edge _ t)).trans
        ((extInterpretation W hW F).freeLift_map_edge _))).trans
      (congrArg F.mapArrow.obj (OneTruncation.arrowMk_globeHomMk_eq _ _
        (Equiv.symm_apply_apply (globeEquiv W hW) t.cell)))

private theorem arrowMk_extFreeLift_map {d : PastingDiagram (sph[W] : DiagSet.{u})}
    {e : PastingDiagram (realize.{u}.obj W.rdc)} (hed : e.Equiv (d.mapTo incl[W]))
    {x y : (sph[W] : DiagSet.{u}).Vertex} {x' y' : (realize.{u}.obj W.rdc).Vertex}
    {p : OneTruncation.point x ⟶ OneTruncation.point y}
    {f : OneTruncation.point x' ⟶ OneTruncation.point y'}
    (hp : IsComposite d p) (hf : IsComposite e f) :
    Arrow.mk ((extInterpretation W hW F).freeLift.map f) =
      Arrow.mk (F.map ((OneTruncation.quotientFunctor _).map p)) :=
  (congrArg (extInterpretation W hW F).freeLift.mapArrow.obj
    (IsComposite.arrowMk_eq hed hf (hp.map incl[W]))).trans
    (congrArg (fun H : OneTruncation.Free (sph[W] : DiagSet.{u}) ⥤ D => Arrow.mk (H.map p))
      (freeMap_comp_extFreeLift W hW F))

include ha hb hF in
private theorem extInterpretation_respects : (extInterpretation W hW F).Respects where
  unit r := by
    have he : edgeBack W hW (DiagSet.Edge.id r) = DiagSet.Edge.id _ :=
      DiagSet.Edge.ext ((globeEquiv W hW).injective
        ((Equiv.apply_symm_apply _ _).trans
          ((congrArg ((realize.{u}.obj W.rdc).map (toAtomPoint (atomGlobe 1)).op)
            (Equiv.apply_symm_apply (vertexEquiv W hW) r).symm).trans
              (NatTrans.naturality_apply incl[W] _ _).symm)))
    exact (congrArg (fun e => F.map (OneTruncation.globeHomMk e)) he).trans
      ((congrArg F.map (OneTruncation.globeHomMk_id _)).trans (F.map_id _))
  boundary {V} hV c _ _ f g hf hg := by
    have hd : (ofCell c).dim = 2 := hV
    refine Arrow.mk_injective _ _ ?_
    rcases realize_cell_cases W (hV.trans hW.symm) c with ⟨c', rfl⟩ | hc
    · obtain ⟨_, _, f₀, g₀, hf₀, hg₀, e⟩ := OneTruncation.exists_boundary_relation hV c'
      have hmap (α : Bool) : ((ofCell c').boundary 1 α).mapTo incl[W] =
          (ofCell (incl[W].app _ c')).boundary 1 α := by
        rw [← boundary_mapTo, ← PastingDiagram.ofCell_app]
      exact (arrowMk_extFreeLift_map W hW F ((hmap false) ▸ .refl _) hf₀ hf).trans
        ((congrArg (fun m => Arrow.mk (F.map m)) e).trans
          (arrowMk_extFreeLift_map W hW F ((hmap true) ▸ .refl _) hg₀ hg).symm)
    · have hea := (hc.boundary 1 false).trans ha
      have heb := (hc.boundary 1 true).trans hb
      have hb₁ (α : Bool) : ((ofCell c).boundary 1 α).dim = 1 :=
        dim_boundary _ (by rw [hd]; omega) α
      obtain ⟨_, _, p, hp⟩ := exists_isComposite_of_dim_eq_one a.toPastingDiagram
        ((dim_eq_of_equiv hea).symm.trans (hb₁ false))
      obtain ⟨_, _, q, hq⟩ := exists_isComposite_of_dim_eq_one b.toPastingDiagram
        ((dim_eq_of_equiv heb).symm.trans (hb₁ true))
      exact (arrowMk_extFreeLift_map W hW F hea hp hf).trans
        ((hF hp hq).trans (arrowMk_extFreeLift_map W hW F heb hq hg).symm)

include hW ha hb hF in
private theorem exists_comp_eq :
    ∃ G : OneTruncation (realize.{u}.obj W.rdc) ⥤ D,
      (oneTruncation.map incl[W]).toFunctor ⋙ G = F :=
  ⟨(extInterpretation W hW F).lift (extInterpretation_respects W hW F a b ha hb hF),
    CategoryTheory.Quotient.lift_unique' _ _ _
      ((congrArg (· ⋙ (extInterpretation W hW F).lift
          (extInterpretation_respects W hW F a b ha hb hF))
        (quotientFunctor_comp_oneTruncation_map incl[W])).trans
        ((congrArg (OneTruncation.freeMap incl[W] ⋙ ·)
          ((extInterpretation W hW F).quotientFunctor_comp_lift
            (extInterpretation_respects W hW F a b ha hb hF))).trans
          (freeMap_comp_extFreeLift W hW F)))⟩

end Extension

open Atoms.Molecule Atoms.Molecule.OGP in
private theorem equiv_boundary_taut_of_emb (W : Atom) {B : MoleculeShape} (g : B.ogp ⟶ W.ogp)
    [IsInclusion g] (hg : OGP.map g ⊤ ≤ W.ogp.bdryFull ⊤) (k : ℕ) (α : Bool)
    (himg : OGP.map g ⊤ = W.ogp.boundary ⊤ k α) (z : diagram (realize.{u}.obj W.rdc) W)
    (hz : (ofCell z).map = 𝟙 (realize.obj W.rdc)) :
    ((ofCell z).boundary k α).Equiv ((restrictAlong (𝟙 _) B g hg).mapTo incl[W]) := by
  have E : RDCpx.ofInclusion (P := B.rdc) (Q := W.rdc) g = RDCpx.ofInclusion (P := B.rdc)
      (Q := W.rdc.restrict (W.ogp.bdryFull ⊤))
      (codRestrict g _ fun x => hg ⟨x, LowerSet.mem_top, rfl⟩) ≫
        W.rdc.restrictIncl (W.ogp.bdryFull ⊤) := by
    ext x
    rfl
  refine equiv_of_emb_of_image_eq (ofCell z).map
    (W.boundaryIncl k α) g rfl ?_ ((W.map_boundaryIncl_top k α).trans himg.symm)
  rw [hz]
  refine (Category.comp_id _).trans
    ((congrArg realize.map E).trans ((realize.map_comp _ _).trans ?_))
  exact congrArg (· ≫ incl[W]) (Category.comp_id _).symm

namespace Parallel

variable {X : DiagSet.{u}} {s t : RoundPastingDiagram X} (h : Parallel s t)

private theorem exists_hasRoundType_of_comp_eq (g : realize.{u}.obj h.cellShape.rdc ⟶ X)
    (hg : incl[h.cellShape] ≫ g = h.sphere) :
    ∃ x : diagram X h.cellShape, HasRoundType (PastingDiagram.ofCell x) s t := by
  refine ⟨uliftYonedaEquiv ((realizeAtomIso h.cellShape).inv ≫ g), ?_⟩
  have hx := (h.hasRoundType_ofCell_iff (𝟙 _)
    (uliftYonedaEquiv ((realizeAtomIso h.cellShape).inv ≫ g))).2 (by
      rw [Category.comp_id, ← hg]
      congr 1
      change (realizeAtomIso h.cellShape).hom ≫ uliftYonedaEquiv.symm _ = g
      rw [Equiv.symm_apply_apply, Iso.hom_inv_id_assoc])
  rwa [RoundPastingDiagram.mapTo_id, RoundPastingDiagram.mapTo_id] at hx

private noncomputable def half (α : Bool) : RoundPastingDiagram (sph[h.cellShape] : DiagSet.{u}) :=
  ⟨restrictAlong (𝟙 _) _ (h.cellShapeEmb α) (h.map_cellShapeEmb_le_bdryFull α),
    by cases α; exacts [s.isRound, t.isRound]⟩

private theorem half_mapTo_sphere (α : Bool) :
    (h.half α).toPastingDiagram.mapTo h.sphere = (cond α t s).toPastingDiagram :=
  (congrArg (PastingDiagram.mk _) (congrArg (· ≫ h.sphere) (Category.comp_id _))).trans
    (h.restrictAlong_sphere α)

private theorem equiv_boundary_taut (hs : s.dim = 1) (α : Bool) :
    ((ofCell (⟨𝟙 _⟩ : diagram (realize.{u}.obj h.cellShape.rdc) h.cellShape)).boundary 1 α).Equiv
      ((h.half α).toPastingDiagram.mapTo incl[h.cellShape]) :=
  equiv_boundary_taut_of_emb _ (h.cellShapeEmb α) (h.map_cellShapeEmb_le_bdryFull α) 1 α
    (by rw [h.map_cellShapeEmb, hs]) _ (ofCell_taut_map _)

end Parallel

open Atoms.Molecule Atoms.Molecule.OGP in
private theorem exists_equiv_paste_restrictTo (u : PastingDiagram X) {V W U : LowerSet u.shape.ogp}
    [DecidablePred (· ∈ V)] [DecidablePred (· ∈ W)] [DecidablePred (· ∈ U)]
    {k : ℕ} (hp : u.shape.ogp.IsPastingIn k V W U) (hV : IsMoleculeIn u.shape.ogp V)
    (hW : IsMoleculeIn u.shape.ogp W) (hU : IsMoleculeIn u.shape.ogp U)
    (hkV : k < (u.restrictTo hV).dim) (hkW : k < (u.restrictTo hW).dim) :
    ∃ hpast : (u.restrictTo hV).Pastable (u.restrictTo hW) k,
      ((u.restrictTo hV).paste (u.restrictTo hW) k hpast).Equiv (u.restrictTo hU) := by
  have hpast : (u.restrictTo hV).Pastable (u.restrictTo hW) k :=
    ⟨(equiv_boundary_restrictTo u hV k true).trans ((equiv_restrictTo_of_eq u _ _
      (hp.inf_eq_output.symm.trans hp.inf_eq_input)).trans
        (equiv_boundary_restrictTo u hW k false).symm), lt_min hkV hkW⟩
  exact ⟨hpast, equiv_paste_of_emb _ _ _ k hpast u.map (u.shape.subIncl _) (u.shape.subIncl hV)
    (u.shape.subIncl hW) rfl rfl rfl (by
      rw [MoleculeShape.map_subIncl_top, MoleculeShape.map_subIncl_top,
        MoleculeShape.map_subIncl_top]
      exact hp)⟩

open Atoms.Molecule Atoms.Molecule.OGP Order in
private theorem exists_isComposite_boundary_restrictTo (u : PastingDiagram X)
    {S : LowerSet u.shape.ogp} (hS : IsMoleculeIn u.shape.ogp S) (h₁ : 1 ≤ krullDim S)
    (h₂ : krullDim S ≤ 2) [hdec : DecidablePred (· ∈ S)] :
    ∃ (a b : X.Vertex) (φ ψ : OneTruncation.point a ⟶ OneTruncation.point b),
      IsComposite (u.restrictTo (hS.boundary 1 false)) φ ∧
        IsComposite (u.restrictTo (hS.boundary 1 true)) ψ ∧
        (OneTruncation.quotientFunctor X).map φ = (OneTruncation.quotientFunctor X).map ψ := by
  revert hdec
  induction hS with
  | point x hx =>
    rw [LowerSet.krullDim_Iic, grade_eq_zero_iff.2 hx] at h₁
    exact absurd h₁ (by norm_num)
  | atom t hround hbdry _ =>
    intro hdec
    rw [LowerSet.krullDim_Iic] at h₁ h₂
    have he : (ofCell (u.cellAt t)).Equiv (u.restrictTo (IsMoleculeIn.atom t hround hbdry)) :=
      (u.equiv_ofCell_cellAt t).trans (@equiv_restrictTo_of_eq _ u _ _
        (fun a => LowerSet.decidableMemIic t a) _ _ _ rfl)
    obtain h1 | h2 : grade ℕ t = 1 ∨ grade ℕ t = 2 := by
      have : 1 ≤ grade ℕ t := by exact_mod_cast h₁
      have : grade ℕ t ≤ 2 := by exact_mod_cast h₂
      omega
    · obtain ⟨a, b, φ, hφ⟩ := exists_isComposite_of_dim_eq_one (ofCell (u.cellAt t))
        ((dimension_principalAtomRDC u.shape.rdc t).trans h1)
      have hc (α : Bool) := hφ.equiv (he.trans (equiv_restrictTo_of_eq u _
        ((IsMoleculeIn.atom t hround hbdry).boundary 1 α)
        (boundary_eq_self (by rw [LowerSet.krullDim_Iic, h1]) α).symm))
      exact ⟨a, b, φ, φ, hc false, hc true, rfl⟩
    · obtain ⟨a, b, φ, ψ, hφ, hψ, e⟩ := OneTruncation.exists_boundary_relation
        ((dimension_principalAtomRDC u.shape.rdc t).trans h2) (u.cellAt t)
      have hb (α : Bool) := (he.boundary 1 α).trans (equiv_boundary_restrictTo u _ 1 α)
      exact ⟨a, b, φ, ψ, hφ.equiv (hb false), hψ.equiv (hb true), e⟩
  | paste k V W U hp hV hW hk ihV ihW =>
    intro hdec
    have hU := IsMoleculeIn.paste k V W U hp hV hW hk
    have : DecidablePred (· ∈ V) := Classical.decPred _
    have : DecidablePred (· ∈ W) := Classical.decPred _
    have hk₂ := lt_min_iff.1 hk
    rw [← dim_restrictTo u hV, ← dim_restrictTo u hW] at hk₂
    have hkV : k < (u.restrictTo hV).dim := by exact_mod_cast hk₂.1
    have hkW : k < (u.restrictTo hW).dim := by exact_mod_cast hk₂.2
    have hdim := dim_eq_of_equiv (exists_equiv_paste_restrictTo u hp hV hW hU hkV hkW).choose_spec
    rw [dim_paste] at hdim
    rw [← dim_restrictTo u hU] at h₂
    have hU₂ : (u.restrictTo hU).dim ≤ 2 := by exact_mod_cast h₂
    have hmV := le_max_left (u.restrictTo hV).dim (u.restrictTo hW).dim
    have hmW := le_max_right (u.restrictTo hV).dim (u.restrictTo hW).dim
    obtain ⟨a, b, φ, ψ, hφ, hψ, e⟩ := ihV
      (by rw [← dim_restrictTo u hV]; exact_mod_cast (by omega : 1 ≤ (u.restrictTo hV).dim))
      (by rw [← dim_restrictTo u hV]; exact_mod_cast (by omega : (u.restrictTo hV).dim ≤ 2))
    obtain ⟨a', b', φ', ψ', hφ', hψ', e'⟩ := ihW
      (by rw [← dim_restrictTo u hW]; exact_mod_cast (by omega : 1 ≤ (u.restrictTo hW).dim))
      (by rw [← dim_restrictTo u hW]; exact_mod_cast (by omega : (u.restrictTo hW).dim ≤ 2))
    rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
    · have hq (α : Bool) := hp.boundary_of_lt hV.isGlobular hW.isGlobular (n := 1) zero_lt_one α
      obtain ⟨hp₀, he₀⟩ := exists_equiv_paste_restrictTo u (hq false) (hV.boundary 1 false)
        (hW.boundary 1 false) (hU.boundary 1 false) (by rw [hφ.hasBdry.dim_h]; exact one_pos)
        (by rw [hφ'.hasBdry.dim_h]; exact one_pos)
      obtain ⟨hp₁, he₁⟩ := exists_equiv_paste_restrictTo u (hq true) (hV.boundary 1 true)
        (hW.boundary 1 true) (hU.boundary 1 true) (by rw [hψ.hasBdry.dim_h]; exact one_pos)
        (by rw [hψ'.hasBdry.dim_h]; exact one_pos)
      obtain rfl : b = a' := ofCell_equiv_ofCell_iff.1
        (hφ.hasBdry.other.symm.trans (hp₀.1.trans hφ'.hasBdry.side))
      exact ⟨a, b', φ ≫ φ', ψ ≫ ψ', (IsComposite.paste hp₀ hφ hφ').equiv he₀,
        (IsComposite.paste hp₁ hψ hψ').equiv he₁, by rw [Functor.map_comp, Functor.map_comp, e, e']⟩
    · have hm : (u.restrictTo (hV.boundary 1 true)).Equiv (u.restrictTo (hW.boundary 1 false)) :=
        equiv_restrictTo_of_eq u _ _ (hp.inf_eq_output.symm.trans hp.inf_eq_input)
      obtain rfl : a = a' := ofCell_equiv_ofCell_iff.1
        (hψ.hasBdry.side.symm.trans ((hm.boundary 0 false).trans hφ'.hasBdry.side))
      obtain rfl : b = b' := ofCell_equiv_ofCell_iff.1
        (hψ.hasBdry.other.symm.trans ((hm.boundary 0 true).trans hφ'.hasBdry.other))
      refine ⟨a, b, φ, ψ', hφ.equiv (equiv_restrictTo_of_eq u _ _ hp.boundary_input.symm),
        hψ'.equiv (equiv_restrictTo_of_eq u _ _ hp.boundary_output.symm), ?_⟩
      rw [e, (hψ.equiv hm).eq hφ', e']

open Atoms.Molecule Atoms.Molecule.OGP Order in
theorem arrowMk_eq_of_isComposite_boundary {u : PastingDiagram X} (hu : u.dim = 2)
    {a b a' b' : X.Vertex}
    {φ : OneTruncation.point a ⟶ OneTruncation.point b}
    {ψ : OneTruncation.point a' ⟶ OneTruncation.point b'}
    (hφ : IsComposite (u.boundary 1 false) φ) (hψ : IsComposite (u.boundary 1 true) ψ) :
    Arrow.mk ((OneTruncation.quotientFunctor X).map φ) =
      Arrow.mk ((OneTruncation.quotientFunctor X).map ψ) := by
  have hd : krullDim (⊤ : LowerSet u.shape.ogp) = 2 := by
    rw [LowerSet.krullDim_top, u.shape.krullDim_eq_dimension, ← dim_def, hu]
    rfl
  obtain ⟨_, _, φ₀, ψ₀, h₀, h₁, e⟩ := exists_isComposite_boundary_restrictTo u u.shape.isMolecule
    (by rw [hd]; exact_mod_cast one_le_two) hd.le
  have hb (α : Bool) := (equiv_boundary_restrictTo u u.shape.isMolecule 1 α).symm.trans
    ((equiv_restrictTo_univ u).boundary 1 α)
  exact (congrArg (OneTruncation.quotientFunctor X).mapArrow.obj
    (IsComposite.arrowMk_eq (.refl _) hφ (h₀.equiv (hb false)))).trans ((congrArg Arrow.mk e).trans
      (congrArg (OneTruncation.quotientFunctor X).mapArrow.obj
        (IsComposite.arrowMk_eq (.refl _) (h₁.equiv (hb true)) hψ)))

private theorem arrowMk_eq_of_hasRoundType {s t : RoundPastingDiagram X} {V : Atom}
    (hV : V.dimension = 2) (x : diagram X V) (hx : HasRoundType (PastingDiagram.ofCell x) s t)
    (hs : s.dim = 1) {a b a' b' : X.Vertex}
    {p : OneTruncation.point a ⟶ OneTruncation.point b}
    {q : OneTruncation.point a' ⟶ OneTruncation.point b'}
    (hp : IsComposite s.toPastingDiagram p) (hq : IsComposite t.toPastingDiagram q) :
    Arrow.mk ((OneTruncation.quotientFunctor X).map p) =
      Arrow.mk ((OneTruncation.quotientFunctor X).map q) := by
  obtain ⟨_, _, f, g, hf, hg, e⟩ := OneTruncation.exists_boundary_relation hV x
  have hxs := hx.source
  have hxt := hx.target
  rw [hs] at hxs hxt
  exact (congrArg (OneTruncation.quotientFunctor X).mapArrow.obj
    (IsComposite.arrowMk_eq hxs.symm hp hf)).trans ((congrArg Arrow.mk e).trans
      (congrArg (OneTruncation.quotientFunctor X).mapArrow.obj
        (IsComposite.arrowMk_eq hxt.symm hq hg)).symm)

theorem Parallel.exists_categoricalNerve_filler_of_arrowMk_eq {C : Cat.{u, u}}
    {s t : RoundPastingDiagram (categoricalNerve.obj C)} (h : Parallel s t) (hs : s.dim = 1)
    (hst : ∀ {a b a' b' : (categoricalNerve.obj C).Vertex}
      {p : OneTruncation.point a ⟶ OneTruncation.point b}
      {q : OneTruncation.point a' ⟶ OneTruncation.point b'},
      IsComposite s.toPastingDiagram p → IsComposite t.toPastingDiagram q →
        Arrow.mk ((OneTruncation.quotientFunctor _).map p) =
          Arrow.mk ((OneTruncation.quotientFunctor _).map q)) :
    ∃ y : diagram (categoricalNerve.obj C) h.cellShape,
      HasRoundType (PastingDiagram.ofCell y) s t := by
  have hW : h.cellShape.dimension = 2 := by rw [h.dimension_cellShape, hs]
  let f := h.sphere
  let F := (oneTruncationAdjunction.homEquiv _ _).symm f
  have hQ : OneTruncation.quotientFunctor _ ⋙ F.toFunctor =
      OneTruncation.freeMap f ⋙ (OneTruncation.quotientFunctor _ ⋙
        (oneTruncationAdjunction.counit.app C).toFunctor) :=
    congrArg (· ⋙ (oneTruncationAdjunction.counit.app C).toFunctor)
      (quotientFunctor_comp_oneTruncation_map f)
  have hF : ∀ {a b a' b' : (sph[h.cellShape] : DiagSet.{u}).Vertex}
      {p : OneTruncation.point a ⟶ OneTruncation.point b}
      {p' : OneTruncation.point a' ⟶ OneTruncation.point b'},
      IsComposite (h.half false).toPastingDiagram p →
        IsComposite (h.half true).toPastingDiagram p' →
        Arrow.mk (F.toFunctor.map ((OneTruncation.quotientFunctor _).map p)) =
          Arrow.mk (F.toFunctor.map ((OneTruncation.quotientFunctor _).map p')) := by
    intro a b a' b' p p' hp hp'
    have e₀ := Eq.subst (motive := fun d => IsComposite d _)
      (h.half_mapTo_sphere false) (hp.map f)
    have e₁ := Eq.subst (motive := fun d => IsComposite d _)
      (h.half_mapTo_sphere true) (hp'.map f)
    have c := hst e₀ e₁
    have cong {a b : (sph[h.cellShape] : DiagSet.{u}).Vertex}
        (γ : OneTruncation.point a ⟶ OneTruncation.point b) :
        Arrow.mk (F.toFunctor.map ((OneTruncation.quotientFunctor _).map γ)) =
          (oneTruncationAdjunction.counit.app C).toFunctor.mapArrow.obj
            (Arrow.mk ((OneTruncation.quotientFunctor _).map ((OneTruncation.freeMap f).map γ))) :=
      congrArg (fun H => Arrow.mk (H.map γ)) hQ
    exact (cong p).trans ((congrArg _ c).trans (cong p').symm)
  obtain ⟨G, hG⟩ := exists_comp_eq h.cellShape hW F.toFunctor (h.half false)
    (h.half true) (h.equiv_boundary_taut hs false) (h.equiv_boundary_taut hs true)
    hF
  refine Parallel.exists_hasRoundType_of_comp_eq h
    (oneTruncationAdjunction.homEquiv _ _ G.toCatHom) ?_
  refine (oneTruncationAdjunction.homEquiv_naturality_left _ _).symm.trans ?_
  exact (congrArg (oneTruncationAdjunction.homEquiv _ _) (Cat.ext hG)).trans
    (Equiv.apply_symm_apply _ _)

theorem Parallel.exists_categoricalNerve_filler_symm {C : Cat.{u, u}}
    {s t : RoundPastingDiagram (categoricalNerve.obj C)} (h : Parallel s t) (hs : s.dim = 1)
    (hst : ∃ x : diagram (categoricalNerve.obj C) h.cellShape,
      HasRoundType (PastingDiagram.ofCell x) s t) :
    ∃ y : diagram (categoricalNerve.obj C) h.symm.cellShape,
      HasRoundType (PastingDiagram.ofCell y) t s := by
  obtain ⟨x, hx⟩ := hst
  have hV : h.cellShape.dimension = 2 := by rw [h.dimension_cellShape, hs]
  exact h.symm.exists_categoricalNerve_filler_of_arrowMk_eq (h.1.symm.trans hs)
    fun hp hq => (arrowMk_eq_of_hasRoundType hV x hx hs hq hp).symm

private theorem exists_categoricalNerve_inverse {C : Cat.{u, u}}
    (e : RoundPastingDiagram (categoricalNerve.obj C)) {n : ℕ} (hn : e.dim = n + 1) (h1 : 1 ≤ n) :
    ∃ (U : Atom) (x : diagram (categoricalNerve.obj C) U), HasRoundType (PastingDiagram.ofCell x)
      ⟨e.boundary n true, isRound_boundary_of_isRound e.isRound n true⟩
      ⟨e.boundary n false, isRound_boundary_of_isRound e.isRound n false⟩ := by
  have hpar := parallel_boundary e.isRound hn true false
  have hb : (e.boundary n true).dim = n := dim_boundary _ (by omega) true
  rcases h1.lt_or_eq with h2 | rfl
  · exact ⟨_, hpar.exists_categoricalNerve_filler (by change 2 ≤ (e.boundary n true).dim; omega)⟩
  · exact ⟨_, hpar.exists_categoricalNerve_filler_of_arrowMk_eq hb fun hφ hψ =>
      (arrowMk_eq_of_isComposite_boundary hn hψ hφ).symm⟩

theorem categoricalNerve_mem_equivalences {C : Cat.{u, u}}
    (e : RoundPastingDiagram (categoricalNerve.obj C)) (he : 2 ≤ e.dim) :
    e ∈ equivalences (categoricalNerve.obj C) := by
  refine subset_equivalences (A := {e | 2 ≤ e.dim}) (fun e he => ?_) he
  have he : 2 ≤ e.dim := he
  obtain ⟨n, hn⟩ : ∃ n, e.dim = n + 1 := ⟨e.dim - 1, by omega⟩
  obtain ⟨U, x, hx⟩ := exists_categoricalNerve_inverse e hn (by omega)
  refine biInvWitness_of_forall_parallel hn (e' := cellRound x) hx fun s t hst hs => ?_
  obtain ⟨z, hz⟩ := hst.exists_categoricalNerve_filler (by omega)
  exact ⟨cellRound z, show 2 ≤ (PastingDiagram.ofCell z).dim by rw [hz.dim_eq]; omega, hz⟩

private theorem arrowMk_eq_of_counit {C : Cat.{u, u}} {p q p' q' : OneTruncation
    (categoricalNerve.obj C)} (m : p ⟶ q) (m' : p' ⟶ q')
    (h : Arrow.mk ((oneTruncationAdjunction.counit.app C).toFunctor.map m) =
      Arrow.mk ((oneTruncationAdjunction.counit.app C).toFunctor.map m')) :
    Arrow.mk m = Arrow.mk m' := by
  have e : (oneTruncationAdjunction.counit.app C).toFunctor ⋙
      (inv (oneTruncationAdjunction.counit.app C)).toFunctor =
        𝟭 (OneTruncation (categoricalNerve.obj C)) :=
    congrArg Cat.Hom.toFunctor (IsIso.hom_inv_id (oneTruncationAdjunction.counit.app C))
  have hm {p q : OneTruncation (categoricalNerve.obj C)} (n : p ⟶ q) : Arrow.mk n =
      ((oneTruncationAdjunction.counit.app C).toFunctor ⋙
        (inv (oneTruncationAdjunction.counit.app C)).toFunctor).mapArrow.obj (Arrow.mk n) := by
    rw [e]
    rfl
  rw [hm m, hm m']
  exact congrArg (inv (oneTruncationAdjunction.counit.app C)).toFunctor.mapArrow.obj h

private theorem exists_edge_categoricalNerve {C : Cat.{u, u}}
    {p q : (DiagSet.toSSet.obj (categoricalNerve.obj C)) _⦋0⦌}
    (f : (oneTruncationAdjunction.counit.app C).toFunctor.obj (OneTruncation.mk p) ⟶
      (oneTruncationAdjunction.counit.app C).toFunctor.obj (OneTruncation.mk q)) :
    ∃ ε : SSet.Edge p q, Arrow.mk ((oneTruncationAdjunction.counit.app C).toFunctor.map
      (OneTruncation.homMk ε)) = Arrow.mk f := by
  let ε := (nerve.edgeMk f).map (nerveToCategoricalNerve C)
  let p' := (nerveToCategoricalNerve C).app (op ⦋0⦌) (nerveEquiv.symm
    ((oneTruncationAdjunction.counit.app C).toFunctor.obj (OneTruncation.mk p)))
  let q' := (nerveToCategoricalNerve C).app (op ⦋0⦌) (nerveEquiv.symm
    ((oneTruncationAdjunction.counit.app C).toFunctor.obj (OneTruncation.mk q)))
  have hε := (arrowMk_oneTruncationAdjunction_counit_app_map_homMk C ε).trans
    (arrowMk_map_toFin_map_tautEdge (ComposableArrows.mk₁ f))
  have hcomp : (oneTruncationAdjunction.counit.app C).toFunctor ⋙
      (inv (oneTruncationAdjunction.counit.app C)).toFunctor =
        𝟭 (OneTruncation (categoricalNerve.obj C)) :=
    congrArg Cat.Hom.toFunctor (IsIso.hom_inv_id (oneTruncationAdjunction.counit.app C))
  have hinj : Function.Injective (oneTruncationAdjunction.counit.app C).toFunctor.obj :=
    fun x y h => (CategoryTheory.Functor.congr_obj hcomp x).symm.trans
      ((congrArg (inv (oneTruncationAdjunction.counit.app C)).toFunctor.obj h).trans
        (CategoryTheory.Functor.congr_obj hcomp y))
  have hp : OneTruncation.mk p' = OneTruncation.mk p := hinj (congrArg Arrow.left hε)
  have hq : OneTruncation.mk q' = OneTruncation.mk q := hinj (congrArg Arrow.right hε)
  have hp' : p' = p :=
    congrArg (fun a => a.as.cell) hp
  have hq' : q' = q :=
    congrArg (fun a => a.as.cell) hq
  let ε' : SSet.Edge p q := SSet.Edge.mk ε.edge (ε.src_eq.trans hp') (ε.tgt_eq.trans hq')
  exact ⟨ε', (congrArg (oneTruncationAdjunction.counit.app C).toFunctor.mapArrow.obj
    (OneTruncation.arrowMk_homMk_eq ε' ε rfl)).trans hε⟩

private theorem hasRoundType_of_isComposite_edge {u : RoundPastingDiagram X}
    {a b : X.Vertex} {φ : OneTruncation.point a ⟶ OneTruncation.point b}
    (hφ : IsComposite u.toPastingDiagram φ) (ε : SSet.Edge (X := DiagSet.toSSet.obj X) a b)
    {V : Atom} (θ : V ≅ simplexFunctor.obj ⦋1⦌) (h0 : u.dim - 1 = 0)
    (hb₀ : (u.boundary (u.dim - 1) false).dim = u.dim - 1)
    (hb₁ : (u.boundary (u.dim - 1) true).dim = u.dim - 1) :
    HasRoundType (PastingDiagram.ofCell (X.map θ.hom.op ε.edge))
      ⟨u.boundary (u.dim - 1) false, isRound_boundary_of_isRound u.isRound _ false⟩
      ⟨u.boundary (u.dim - 1) true, isRound_boundary_of_isRound u.isRound _ true⟩ := by
  have hce := PastingDiagram.equiv_ofCell_map_iso θ ε.edge
  refine .of_equiv_boundary hb₀ hb₁ ((dim_eq_of_equiv hce).trans (by
    rw [h0]; exact dimension_atomSimplex 1)) fun β => ?_
  refine (hce.boundary _ β).trans ((PastingDiagram.equiv_of_eq
    ((PastingDiagram.ofCell (X := X) ε.edge).boundary_congr h0 β)).trans
      ?_)
  cases β
  · exact (OneTruncation.isComposite_simplex_edge ε).hasBdry.side.trans (hφ.hasBdry.side.symm.trans
      (PastingDiagram.equiv_of_eq (u.toPastingDiagram.boundary_congr h0 false).symm))
  · exact (OneTruncation.isComposite_simplex_edge ε).hasBdry.other.trans
      (hφ.hasBdry.other.symm.trans
      (PastingDiagram.equiv_of_eq (u.toPastingDiagram.boundary_congr h0 true).symm))

theorem hasWeakComposites_categoricalNerve (C : Cat.{u, u}) :
    HasWeakComposites (categoricalNerve.obj C) := by
  refine (hasWeakComposites_iff_positive _).2 fun u hu => ?_
  have hn : u.dim = (u.dim - 1) + 1 := (Nat.sub_add_cancel hu).symm
  have hb (α : Bool) : (u.boundary (u.dim - 1) α).dim = u.dim - 1 :=
    dim_boundary _ (Nat.sub_le _ _) α
  have hpar := parallel_boundary u.isRound hn false true
  rcases (show u.dim = 1 ∨ 2 ≤ u.dim by omega) with h1 | h2
  · obtain ⟨a, b, φ, hφ⟩ := exists_isComposite_of_dim_eq_one u.toPastingDiagram h1
    obtain ⟨ε, hε⟩ := exists_edge_categoricalNerve (p := a) (q := b)
      ((oneTruncationAdjunction.counit.app C).toFunctor.map
        ((OneTruncation.quotientFunctor _).map φ))
    obtain ⟨θ⟩ : Nonempty (hpar.cellShape ≅ simplexFunctor.obj ⦋1⦌) :=
      (nonempty_iso_atomGlobe_of_dimension_eq_one
        (hpar.dimension_cellShape.trans (by rw [hb false, h1]))).map
          fun i => i.symm ≪≫ atomSimplexOneIsoGlobe.symm
    have hce := PastingDiagram.equiv_ofCell_map_iso (X := categoricalNerve.obj C) θ ε.edge
    have h0 : u.dim - 1 = 0 := by omega
    have hc' := hasRoundType_of_isComposite_edge hφ ε θ h0 (hb false) (hb true)
    refine exists_weakComposite_of_cell u hu hpar hc' fun c hc hpu => ?_
    have hεc := (OneTruncation.isComposite_simplex_edge (X := categoricalNerve.obj C) ε).equiv
      (hce.symm.trans hc.symm)
    obtain ⟨w, hw⟩ := hpu.exists_categoricalNerve_filler_of_arrowMk_eq h1 fun hφ' hψ' =>
      (congrArg (OneTruncation.quotientFunctor _).mapArrow.obj
        (IsComposite.arrowMk_eq (.refl _) hφ' hφ)).trans ((arrowMk_eq_of_counit _ _ hε.symm).trans
          (congrArg (OneTruncation.quotientFunctor _).mapArrow.obj
            (IsComposite.arrowMk_eq (.refl _) hεc hψ')))
    exact Equivalent.of_hasRoundType hw
      (categoricalNerve_mem_equivalences _
        (show 2 ≤ (PastingDiagram.ofCell w).dim by rw [hw.dim_eq, h1]))
  · obtain ⟨c', hc'⟩ : ∃ c' : diagram (categoricalNerve.obj C) hpar.cellShape,
        HasRoundType (PastingDiagram.ofCell c') _ _ := by
      rcases h2.lt_or_eq with h3 | h2
      · exact hpar.exists_categoricalNerve_filler (by rw [hb false]; omega)
      · have h1 : u.dim - 1 = 1 := by omega
        refine hpar.exists_categoricalNerve_filler_of_arrowMk_eq (by rw [hb false]; omega)
          fun hφ hψ => ?_
        exact arrowMk_eq_of_isComposite_boundary h2.symm
          (hφ.equiv (PastingDiagram.equiv_of_eq (u.toPastingDiagram.boundary_congr h1 false)))
          (hψ.equiv (PastingDiagram.equiv_of_eq (u.toPastingDiagram.boundary_congr h1 true)))
    refine exists_weakComposite_of_cell u hu hpar hc' fun c _ hpu => ?_
    obtain ⟨w, hw⟩ := hpu.exists_categoricalNerve_filler h2
    exact Equivalent.of_hasRoundType hw (categoricalNerve_mem_equivalences _
      (show 2 ≤ (PastingDiagram.ofCell w).dim by rw [hw.dim_eq]; omega))

theorem isInftyCategory_one_categoricalNerve (C : Cat.{u, u}) :
    IsInftyCategory 1 (categoricalNerve.obj C) :=
  ⟨hasWeakComposites_categoricalNerve C, fun U x hU =>
    categoricalNerve_mem_equivalences (cellRound x) (show 1 < U.dimension by exact_mod_cast hU)⟩

theorem isFibrant_categoricalNerve (C : Cat.{u, u}) :
    HomotopicalAlgebra.IsFibrant ((DiagSet.toInfty 1).obj (categoricalNerve.obj C)) :=
  (isFibrant_infty_iff 1 _).2 (isInftyCategory_one_categoricalNerve C)

end Atoms.Diagrammatic
