import Atoms.Diagrammatic.Marked.Basic
import Atoms.Diagrammatic.RealizationColimits
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.Nerve
import Atoms.Homotopical.Marked.Cellular
import Atoms.Homotopical.Simplicial.Marked
import Atoms.Molecule.Construction.GrayProductMolecule

open CategoryTheory Limits Opposite MorphismProperty Simplicial
open Atoms.Homotopical Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape

universe w w' u

namespace Atoms.Diagrammatic

def faceMarking (P : RDCpx.{0}) (M : Set P.obj.toOGP) :
    MarkedPresheaf.Marking edgeMarking (nerve (ULift.{u} P.obj.toOGP)) where
  marked n := {e | n.len = 1 ∧
    (P.obj.toOGP.boundary (.Iic e.left.down) 0 true =
        P.obj.toOGP.boundary (.Iic e.right.down) 0 true ∨
      e.right.down ∈ M ∧ grade ℕ e.right.down = 1)}
  markable _ _ h := h.1
  degenerate a b p hp y := by
    refine ⟨hp.1, Or.inl ?_⟩
    have h : p.toOrderHom 0 = p.toOrderHom (Fin.last _) := by
      have h0 := (p.toOrderHom 0).isLt
      have h1 := (p.toOrderHom (Fin.last _)).isLt
      have h2 : b.len = 0 := hp.2
      ext
      omega
    change P.obj.toOGP.boundary (.Iic (y.obj (p.toOrderHom 0)).down) 0 true =
      P.obj.toOGP.boundary (.Iic (y.obj (p.toOrderHom (Fin.last _))).down) 0 true
    rw [h]
  transport a b e x := by
    obtain rfl : a = b := SimplexCategory.ext (SimplexCategory.len_eq_of_isIso e.hom)
    rw [SimplexCategory.eq_id_of_isIso e.hom, op_id, Functor.map_id_apply]

theorem boundary_closure_apply_eq {P Q : OGP.{0}} {f : P → Q} (hf : IsMap f) {x y : P}
    (h : P.boundary (.Iic x) 0 true = P.boundary (.Iic y) 0 true) :
    Q.boundary (.Iic (f x)) 0 true = Q.boundary (.Iic (f y)) 0 true :=
  SetLike.coe_injective (by rw [← hf.image_boundary, ← hf.image_boundary, h])

theorem nerveMap_app_mem_faceMarking {P Q : RDCpx.{0}} {f : P.obj.toOGP → Q.obj.toOGP}
    (hf : IsMap f) {M : Set P.obj.toOGP} {N : Set Q.obj.toOGP}
    (hMN : ∀ x y, y ∈ M → grade ℕ y = 1 → f x = f y ∨ f y ∈ N ∧ grade ℕ (f y) = 1)
    (n : SimplexCategory) (e : (nerve (ULift.{u} P.obj.toOGP)).obj (op n))
    (he : e ∈ (faceMarking P M).marked n) :
    (nerveMap (Monotone.functor (f := ULift.map f) fun _ _ h => hf.monotone h)).app (op n) e ∈
      (faceMarking Q N).marked n := by
  obtain ⟨hn, h | ⟨hM, hd⟩⟩ := he
  · exact ⟨hn, Or.inl (boundary_closure_apply_eq hf h)⟩
  · refine ⟨hn, ?_⟩
    rcases hMN e.left.down _ hM hd with heq | hN
    · exact Or.inl (congrArg (fun z => Q.obj.toOGP.boundary (.Iic z) 0 true) heq)
    · exact Or.inr hN

noncomputable def rdcFaceNerve : RDCpx.{0} ⥤ MarkedSSet where
  obj P := MarkedPresheaf.ofMarking (nerve (ULift.{u} P.obj.toOGP)) (faceMarking P ∅)
  map f := MarkedPresheaf.homMk (nerveMap (Monotone.functor
      (f := ULift.map (ConcreteCategory.hom f.hom)) fun _ _ h =>
        (ConcreteCategory.hom f.hom).isMap.monotone h))
    fun n e he => (MarkedPresheaf.mem_marked_ofMarking _ _ n _).2
      (nerveMap_app_mem_faceMarking (ConcreteCategory.hom f.hom).isMap
        (fun _ _ h => absurd h (Set.notMem_empty _)) n e
        ((MarkedPresheaf.mem_marked_ofMarking _ _ n _).1 he))
  map_id _ := MarkedPresheaf.hom_ext rfl
  map_comp _ _ := MarkedPresheaf.hom_ext rfl

theorem eq_top_of_isMax {U : Atom} {w : U.ogp} (hw : IsMax w) : w = U.top :=
  le_antisymm (U.le_top w) (hw (U.le_top w))

theorem apply_eq_of_degeneracy {U V : Atom} {p : U ⟶ V} (hp : degeneracies p)
    (hU : U.dimension = 1) (z w : U.ogp) : p z = p w := by
  have hle := dimension_le_of_isCollapseHom p hp.1
  have hV : V.dimension = 0 := by
    by_contra h
    exact hp.2 (isIso_of_isCollapseHom_of_dimension_eq p hp.1 (by omega))
  have key : ∀ u : V.ogp, u = V.top := fun u =>
    GradeOrder.eq_of_le_of_grade_le (V.le_top u) (by rw [← V.dimension_eq, hV]; exact Nat.zero_le _)
  rw [key (p z), key (p w)]

private theorem faceMarking_map_cond {x y : MarkedSite atomMarking} (g : x ⟶ y)
    (z w : x.obj.ogp) (hw : x.isMarked = true ∧ IsMax w) (hd : grade ℕ w = 1) :
    g.1 z = g.1 w ∨ (y.isMarked = true ∧ IsMax (g.1 w)) ∧ grade ℕ (g.1 w) = 1 := by
  obtain rfl := eq_top_of_isMax hw.2
  rcases g.2 hw.1 with ⟨hy, hiso⟩ | ⟨c, p, q, hp, hpq⟩
  · have hcol : IsCollapseHom g.1 := isCollapseHom_of_iso (asIso g.1)
    have htop := le_apply_top_of_isCollapseHom g.1 hcol
    have hgt : g.1 x.obj.top = y.obj.top := le_antisymm (y.obj.le_top _) (htop _)
    refine Or.inr ⟨⟨hy, fun u _ => htop u⟩, ?_⟩
    rw [hgt, ← Atom.dimension_eq, ← Atom.dimension_eq_of_iso (asIso g.1), Atom.dimension_eq, hd]
  · left
    rw [← hpq]
    exact congrArg q (apply_eq_of_degeneracy hp (by rw [Atom.dimension_eq, hd]) z _)

noncomputable def markedFaceNerveSite : MarkedSite atomMarking ⥤ MarkedSSet where
  obj x := MarkedPresheaf.ofMarking (nerve (ULift.{u} (atomToRDCpx.obj x.obj).obj.toOGP))
    (faceMarking (atomToRDCpx.obj x.obj) {y | x.isMarked = true ∧ IsMax y})
  map {x y} g := MarkedPresheaf.homMk (nerveMap (Monotone.functor (f := ULift.map g.1)
      fun _ _ h => (Atom.isMap g.1).monotone h)) fun n e he =>
    (MarkedPresheaf.mem_marked_ofMarking _ _ n _).2 (nerveMap_app_mem_faceMarking
      (P := atomToRDCpx.obj x.obj) (Q := atomToRDCpx.obj y.obj)
      (M := {z | x.isMarked = true ∧ IsMax z}) (N := {z | y.isMarked = true ∧ IsMax z})
      (Atom.isMap g.1) (faceMarking_map_cond g) n e
      ((MarkedPresheaf.mem_marked_ofMarking _ _ n _).1 he))
  map_id _ := MarkedPresheaf.hom_ext rfl
  map_comp _ _ := MarkedPresheaf.hom_ext rfl

private noncomputable def faceMarkingHom (U : Atom) {M N : Set U.ogp}
    (h : ∀ x y, y ∈ M → grade ℕ y = 1 → x = y ∨ y ∈ N ∧ grade ℕ y = 1) :
    MarkedPresheaf.ofMarking (nerve (ULift.{u} (atomToRDCpx.obj U).obj.toOGP))
        (faceMarking (atomToRDCpx.obj U) M) ⟶
      MarkedPresheaf.ofMarking (nerve (ULift.{u} (atomToRDCpx.obj U).obj.toOGP))
        (faceMarking (atomToRDCpx.obj U) N) :=
  MarkedPresheaf.homMk (𝟙 _) fun n e he =>
    (MarkedPresheaf.mem_marked_ofMarking _ _ n _).2 (nerveMap_app_mem_faceMarking
      (P := atomToRDCpx.obj U) (Q := atomToRDCpx.obj U) (IsMap.id _) h n e
      ((MarkedPresheaf.mem_marked_ofMarking _ _ n _).1 he))

noncomputable def unmarkedCompMarkedFaceNerveSiteIso :
    MarkedSite.unmarked atomMarking ⋙ markedFaceNerveSite.{u} ≅ atomToRDCpx ⋙ rdcFaceNerve :=
  NatIso.ofComponents (fun U =>
    { hom := faceMarkingHom U fun _ _ h => absurd h.1 Bool.false_ne_true
      inv := faceMarkingHom U fun _ _ h => absurd h (Set.notMem_empty _)
      hom_inv_id := MarkedPresheaf.hom_ext rfl
      inv_hom_id := MarkedPresheaf.hom_ext rfl })
    fun _ => MarkedPresheaf.hom_ext rfl

theorem forget_map_unmarkedCompMarkedFaceNerveSiteIso_hom_app (U : Atom) :
    MarkedPresheaf.forget.map (unmarkedCompMarkedFaceNerveSiteIso.{u}.hom.app U) = 𝟙 _ :=
  rfl

instance epi_markedFaceNerveSite_map_toSelf (x : MarkedSite atomMarking) :
    Epi (markedFaceNerveSite.{u}.map (MarkedSite.toSelf x)) :=
  MarkedPresheaf.forget.epi_of_epi_map ⟨fun _ _ hgh => hgh⟩

theorem isIso_markedFaceNerveSite_map_toSelf (U : Atom) (hU : 0 < U.dimension)
    (h1 : U.dimension ≠ 1) :
    IsIso (markedFaceNerveSite.{u}.map (MarkedSite.toSelf (MarkedSite.marked U hU))) :=
  ⟨faceMarkingHom U (fun _ y hy hd => absurd ((eq_top_of_isMax hy.2) ▸ hd)
      (by rwa [← U.dimension_eq])),
    MarkedPresheaf.hom_ext rfl, MarkedPresheaf.hom_ext rfl⟩

noncomputable def markedFaceNerve : MarkedDiagSet.{u} ⥤ MarkedSSet :=
  MarkedPresheaf.extend markedFaceNerveSite

noncomputable def faceNerve : DiagSet.{u} ⥤ MarkedSSet :=
  MarkedPresheaf.flat atomMarking ⋙ markedFaceNerve

noncomputable def markedFaceNerveAdjunction :
    markedFaceNerve.{u} ⊣ MarkedPresheaf.nerve markedFaceNerveSite
      (fun x => epi_markedFaceNerveSite_map_toSelf x) :=
  MarkedPresheaf.extendAdjunction _ _

section Principal

variable (P : RDCpx.{0}) [DecidableLE P.obj.toOGP]
  [∀ x : P.obj.toOGP, FinEnum (P.obj.toOGP.restrict (.Iic x))]

def principalCoconeRDC : Cocone (principalDiagramRDC P ⋙ atomToRDCpx) where
  pt := P
  ι :=
    { app x := principalInclusionRDC P x
      naturality _ _ f := (principalMapRDC_comp_principalInclusionRDC P (leOfHom f)).trans
        (Category.comp_id _).symm }

private def principalToIic (x : P.obj.toOGP) :
    ULift.{u} (principalAtomRDC P x).ogp → Set.Iic (ULift.up.{u} x) :=
  fun a => ⟨ULift.up (ConcreteCategory.hom (principalInclusionRDC P x).hom a.down),
    LowerSet.mem_Iic_iff.1 (principalInclusionRDC_mem_closure P x a.down)⟩

private def principalOfIic (x : P.obj.toOGP) :
    Set.Iic (ULift.up.{u} x) → ULift.{u} (principalAtomRDC P x).ogp :=
  fun z => ULift.up ((principalAtomIsoRDC P x).hom ⟨z.1.down, LowerSet.mem_Iic_iff.2 z.2⟩)

private theorem monotone_principalToIic (x : P.obj.toOGP) : Monotone (principalToIic.{u} P x) :=
  fun _ _ h => (ConcreteCategory.hom (principalInclusionRDC P x).hom).isMap.monotone h

private theorem monotone_principalOfIic (x : P.obj.toOGP) : Monotone (principalOfIic.{u} P x) :=
  fun _ _ h => (isMorphism (principalAtomIsoRDC P x).hom).monotone h

private theorem principalOfIic_principalToIic (x : P.obj.toOGP)
    (a : ULift.{u} (principalAtomRDC P x).ogp) : principalOfIic P x (principalToIic P x a) = a :=
  ULift.ext _ _ ((principalAtomIsoRDC P x).inv_hom_id_apply a.down)

private theorem principalToIic_principalOfIic (x : P.obj.toOGP) (z : Set.Iic (ULift.up.{u} x)) :
    principalToIic P x (principalOfIic P x z) = z :=
  Subtype.ext (ULift.ext _ _ (principalInclusionRDC_apply_principalAtomIsoRDC P x _))

private noncomputable def principalNerveIso :
    (principalDiagramRDC P ⋙ atomToRDCpx) ⋙ rdcFaceNerve ⋙ MarkedPresheaf.forget ≅
      ULift.orderIso.symm.equivalence.functor ⋙ iicNerveDiagram (ULift.{u} P.obj.toOGP) :=
  NatIso.ofComponents (fun x =>
    { hom := nerveMap (monotone_principalToIic P x).functor
      inv := nerveMap (monotone_principalOfIic P x).functor
      hom_inv_id := nerveMap_functor_eq ((monotone_principalOfIic P x).comp
        (monotone_principalToIic P x)) monotone_id (principalOfIic_principalToIic P x)
      inv_hom_id := nerveMap_functor_eq ((monotone_principalToIic P x).comp
        (monotone_principalOfIic P x)) monotone_id (principalToIic_principalOfIic P x) })
    fun {x y} f => nerveMap_functor_eq
      (f := fun (a : ULift.{u} (principalAtomRDC P x).ogp) =>
        principalToIic P y (ULift.map (principalMapRDC P (leOfHom f)) a))
      (g := fun a => Set.inclusion (Set.Iic_subset_Iic.2 (ULift.up_le.2 (leOfHom f)))
        (principalToIic P x a))
      ((monotone_principalToIic P y).comp
        fun _ _ h => (Atom.isMap (principalMapRDC P (leOfHom f))).monotone h)
      (fun _ _ h => monotone_principalToIic P x h)
      fun a => Subtype.ext (ULift.ext _ _ (congrArg
        (fun g : atomToRDCpx.obj _ ⟶ P => ConcreteCategory.hom g.hom a.down)
        (principalMapRDC_comp_principalInclusionRDC P (leOfHom f))))

private noncomputable def isColimitForgetMapCoconeRdcFaceNerve :
    IsColimit (MarkedPresheaf.forget.mapCocone
      (rdcFaceNerve.{u}.mapCocone (principalCoconeRDC P))) :=
  IsColimit.ofIsoColimit ((IsColimit.precomposeHomEquiv (principalNerveIso P) _).symm
    ((isColimitIicNerveCocone (X := ULift.{u} P.obj.toOGP)).whiskerEquivalence
      ULift.orderIso.symm.equivalence))
    (Cocone.ext (Iso.refl _) fun _ => Category.comp_id _)

private theorem boundary_closure_principalOfIic {x : P.obj.toOGP}
    (z w : Set.Iic (ULift.up.{u} x))
    (h : P.obj.toOGP.boundary (.Iic z.1.down) 0 true =
      P.obj.toOGP.boundary (.Iic w.1.down) 0 true) :
    (principalAtomRDC P x).ogp.boundary (.Iic (principalOfIic P x z).down) 0 true =
      (principalAtomRDC P x).ogp.boundary (.Iic (principalOfIic P x w).down) 0 true := by
  refine map_injective (principalInclusionOGP P x) ?_
  have hz : principalInclusionOGP P x (principalOfIic P x z).down = z.1.down :=
    congrArg (fun a => a.1.down) (principalToIic_principalOfIic P x z)
  have hw : principalInclusionOGP P x (principalOfIic P x w).down = w.1.down :=
    congrArg (fun a => a.1.down) (principalToIic_principalOfIic P x w)
  rw [map_boundary, map_boundary, map_Iic, map_Iic, hz, hw]
  exact h

noncomputable def isColimitRdcFaceNerveMapCocone :
    IsColimit (rdcFaceNerve.{u}.mapCocone (principalCoconeRDC P)) :=
  MarkedPresheaf.isColimitOfForget _ (isColimitForgetMapCoconeRdcFaceNerve P) fun a e he => by
    obtain ⟨hn, h | ⟨hM, -⟩⟩ := (MarkedPresheaf.mem_marked_ofMarking _ _ a _).1 he
    · refine ⟨e.right.down, (nerveMap (monotone_principalOfIic P _).functor).app (op a)
        (nerveIicLift (X := ULift.{u} P.obj.toOGP) (n := op a) e), ?_, ?_⟩
      · exact (MarkedPresheaf.mem_marked_ofMarking _ _ a _).2
          ⟨hn, Or.inl (boundary_closure_principalOfIic P _ _ h)⟩
      · exact nerve.ext_of_isThin (funext fun i =>
          congrArg Subtype.val (principalToIic_principalOfIic P _ _))
    · exact absurd hM (Set.notMem_empty _)

end Principal

instance preservesColimits_markedFaceNerve :
    PreservesColimitsOfSize.{w, w'} markedFaceNerve.{u} :=
  markedFaceNerveAdjunction.leftAdjoint_preservesColimits

instance preservesColimits_faceNerve : PreservesColimitsOfSize.{w, w'} faceNerve.{u} :=
  have : PreservesColimitsOfSize.{w, w'} (MarkedPresheaf.flat.{u, 0} atomMarking) :=
    (MarkedPresheaf.flatForgetAdjunction atomMarking).leftAdjoint_preservesColimits
  inferInstanceAs (PreservesColimitsOfSize.{w, w'}
    (MarkedPresheaf.flat atomMarking ⋙ markedFaceNerve))

noncomputable def yonedaCompFaceNerveIso :
    uliftYoneda.{u} ⋙ faceNerve ≅ atomToRDCpx ⋙ rdcFaceNerve :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (MarkedPresheaf.yonedaCompFlatIso atomMarking) _ ≪≫
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (MarkedPresheaf.yonedaCompExtendIso markedFaceNerveSite) ≪≫
          unmarkedCompMarkedFaceNerveSiteIso

section Realization

variable (P : RDCpx.{0}) [DecidableLE P.obj.toOGP]
  [∀ x : P.obj.toOGP, FinEnum (P.obj.toOGP.restrict (.Iic x))]

private noncomputable def faceNerveRealizeCocone :
    Cocone ((principalDiagramRDC P ⋙ atomToRDCpx) ⋙ rdcFaceNerve.{u}) :=
  (Cocone.precompose
    (Functor.isoWhiskerLeft (principalDiagramRDC P) yonedaCompFaceNerveIso).inv).obj
    (faceNerve.mapCocone (realizeCocone P))

private noncomputable def isColimitFaceNerveRealizeCocone :
    IsColimit (faceNerveRealizeCocone.{u} P) :=
  (IsColimit.precomposeInvEquiv _ _).symm
    (isColimitOfPreserves faceNerve (isColimitRealizeCocone P))

private noncomputable def faceNerveRealizeIso :
    faceNerve.{u}.obj (realize.obj P) ≅ rdcFaceNerve.obj P :=
  IsColimit.coconePointUniqueUpToIso (isColimitFaceNerveRealizeCocone P)
    (isColimitRdcFaceNerveMapCocone P)

private theorem faceNerveRealizeCocone_ι_app (x : P.obj.toOGP) :
    (faceNerveRealizeCocone P).ι.app x = yonedaCompFaceNerveIso.{u}.inv.app (principalAtomRDC P x) ≫
      faceNerve.map ((uliftYonedaEquiv (F := realize.obj P)).symm ⟨principalInclusionRDC P x⟩) := by
  change yonedaCompFaceNerveIso.inv.app _ ≫ faceNerve.map _ = _
  rfl

private theorem faceNerve_map_comp_faceNerveRealizeIso_hom {T : Atom}
    (g : atomToRDCpx.obj T ⟶ P) :
    yonedaCompFaceNerveIso.{u}.inv.app T ≫
      faceNerve.map ((uliftYonedaEquiv (F := realize.obj P)).symm ⟨g⟩) ≫
      (faceNerveRealizeIso P).hom = rdcFaceNerve.map g := by
  have hg := principalLiftRDC_comp_principalInclusionRDC P _ g (hom_apply_mem_closure_apply_top g)
  set L := principalLiftRDC P _ g (hom_apply_mem_closure_apply_top g)
  have hr : (uliftYonedaEquiv (F := realize.obj P)).symm ⟨g⟩ =
      uliftYoneda.{u}.map L ≫ (uliftYonedaEquiv (F := realize.obj P)).symm
        ⟨principalInclusionRDC P (ConcreteCategory.hom g.hom T.top)⟩ :=
    uliftYonedaEquiv.injective ((Equiv.apply_symm_apply _ _).trans (congrArg ULift.up hg.symm))
  have hc := IsColimit.comp_coconePointUniqueUpToIso_hom (isColimitFaceNerveRealizeCocone P)
    (isColimitRdcFaceNerveMapCocone P) (ConcreteCategory.hom g.hom T.top)
  rw [faceNerveRealizeCocone_ι_app] at hc
  have hn := yonedaCompFaceNerveIso.inv.naturality L
  rw [Functor.comp_map, Functor.comp_map] at hn
  refine Eq.trans ?_ (congrArg rdcFaceNerve.map hg)
  simp only [hr, Functor.map_comp, Category.assoc]
  simp only [← Category.assoc] at hc ⊢
  rw [← hn]
  simp only [Category.assoc]
  exact congrArg (rdcFaceNerve.map (atomToRDCpx.map L) ≫ ·) hc

end Realization

private theorem faceNerve_map_realize_map_comp_faceNerveRealizeIso_hom {P Q : RDCpx.{0}}
    [DecidableLE P.obj.toOGP] [∀ x : P.obj.toOGP, FinEnum (P.obj.toOGP.restrict (.Iic x))]
    [DecidableLE Q.obj.toOGP] [∀ y : Q.obj.toOGP, FinEnum (Q.obj.toOGP.restrict (.Iic y))]
    (f : P ⟶ Q) :
    faceNerve.{u}.map (realize.map f) ≫ (faceNerveRealizeIso Q).hom =
      (faceNerveRealizeIso P).hom ≫ rdcFaceNerve.map f := by
  refine (isColimitFaceNerveRealizeCocone P).hom_ext fun x => ?_
  have hc := IsColimit.comp_coconePointUniqueUpToIso_hom (isColimitFaceNerveRealizeCocone P)
    (isColimitRdcFaceNerveMapCocone P) x
  have h1 : (faceNerveRealizeCocone P).ι.app x ≫ faceNerve.map (realize.map f) =
      yonedaCompFaceNerveIso.inv.app (principalAtomRDC P x) ≫
        faceNerve.map ((uliftYonedaEquiv (F := realize.obj P)).symm ⟨principalInclusionRDC P x⟩ ≫
          realize.map f) :=
    (congrArg (· ≫ faceNerve.map (realize.map f)) (faceNerveRealizeCocone_ι_app P x)).trans
      ((Category.assoc _ _ _).trans
        (congrArg (yonedaCompFaceNerveIso.inv.app _ ≫ ·) (faceNerve.map_comp _ _).symm))
  have h2 := faceNerve_map_comp_faceNerveRealizeIso_hom Q (principalInclusionRDC P x ≫ f)
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (faceNerveRealizeIso Q).hom) h1).trans
    ((Category.assoc _ _ _).trans (h2.trans ?_)))
  refine (rdcFaceNerve.map_comp _ _).trans ((congrArg (· ≫ rdcFaceNerve.map f) hc.symm).trans ?_)
  exact Category.assoc _ _ _

@[instance_reducible] private noncomputable def finEnumClosure (P : RDCpx.{0}) (x : P.obj.toOGP) :
    FinEnum (P.obj.toOGP.restrict (.Iic x)) :=
  have : Fintype (P.obj.toOGP.restrict (.Iic x)) := (IsMoleculeIn.finite (P.obj.isRDC x)).fintype
  FinEnum.ofEquiv _ (Fintype.equivFin _)

open Classical in
noncomputable def realizeCompFaceNerveIso : realize.{u} ⋙ faceNerve ≅ rdcFaceNerve :=
  letI (P : RDCpx.{0}) (x : P.obj.toOGP) : FinEnum (P.obj.toOGP.restrict (.Iic x)) :=
    finEnumClosure P x
  NatIso.ofComponents (fun P => faceNerveRealizeIso P)
    fun f => faceNerve_map_realize_map_comp_faceNerveRealizeIso_hom f

open Classical in
theorem faceNerve_map_comp_realizeCompFaceNerveIso_hom_app {P : RDCpx.{0}} {T : Atom}
    (g : atomToRDCpx.obj T ⟶ P) :
    yonedaCompFaceNerveIso.{u}.inv.app T ≫
      faceNerve.map ((uliftYonedaEquiv (F := realize.obj P)).symm ⟨g⟩) ≫
      realizeCompFaceNerveIso.hom.app P = rdcFaceNerve.map g :=
  letI (P : RDCpx.{0}) (x : P.obj.toOGP) : FinEnum (P.obj.toOGP.restrict (.Iic x)) :=
    finEnumClosure P x
  faceNerve_map_comp_faceNerveRealizeIso_hom P g

theorem mono_rdcFaceNerve_map {P Q : RDCpx.{0}} (f : P ⟶ Q)
    (hf : Function.Injective (ConcreteCategory.hom f.hom)) : Mono (rdcFaceNerve.{u}.map f) := by
  rw [MarkedPresheaf.mono_iff, NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  intro σ τ h
  exact nerve.ext_of_isThin (funext fun i => ULift.ext _ _ (hf (congrArg
    (fun ρ : (nerve (ULift.{u} Q.obj.toOGP)).obj n => (ρ.obj i).down) h)))

private theorem mono_faceNerve_map_realize_map {P Q : RDCpx.{0}} (f : P ⟶ Q)
    (hf : Function.Injective (ConcreteCategory.hom f.hom)) :
    Mono (faceNerve.{u}.map (realize.map f)) := by
  have := mono_rdcFaceNerve_map f hf
  have h := realizeCompFaceNerveIso.hom.naturality f
  have : Mono (faceNerve.map (realize.map f) ≫ realizeCompFaceNerveIso.hom.app Q) := by
    rw [Functor.comp_map] at h
    rw [h]
    infer_instance
  exact mono_of_mono _ (realizeCompFaceNerveIso.hom.app Q)

private theorem mono_faceNerve_map_closedSubpresheaf_ι (U : Atom) (S : LowerSet U.ogp) :
    Mono (faceNerve.{u}.map (closedSubpresheaf U S).ι) := by
  let e : Arrow.mk (realize.map (RDCpx.restrictIncl (atomToRDCpx.obj U) S)) ≅
      Arrow.mk (closedSubpresheaf U S).ι :=
    Arrow.isoMk (realizeRestrictIso (atomToRDCpx.obj U) S _ rfl ≪≫ realizeSubsetAtomIso U S)
      (realizeAtomIso U)
        (by ext T g; rfl)
  exact ((MorphismProperty.monomorphisms _).arrow_mk_iso_iff (faceNerve.mapArrow.mapIso e)).1
    (mono_faceNerve_map_realize_map _ Subtype.val_injective)

private theorem mono_faceNerve_map_sphereInclusion (U : Atom) :
    Mono (faceNerve.{u}.map (sphereInclusion U)) := by
  have h := mono_faceNerve_map_closedSubpresheaf_ι U (U.ogp.bdryFull ⊤)
  rwa [closedSubpresheaf_univ_erase_top] at h

instance preservesMonomorphisms_markedFaceNerve : markedFaceNerve.{u}.PreservesMonomorphisms where
  preserves f hf := by
    have hI := MarkedPresheaf.saturation_functorImage_flat_sup_markingMaps atomMarking
      monomorphisms_eq_saturation_sphereInclusions.symm
    have hle : saturation.{u} (functorImage (MarkedPresheaf.flat atomMarking) sphereInclusions ⊔
        MarkedPresheaf.markingMaps atomMarking) ≤
        (monomorphisms MarkedSSet).inverseImage markedFaceNerve := by
      refine saturation_le _ _ (sup_le ?_ ?_)
      · rintro _ _ g ⟨_, _, _, ⟨U⟩, e⟩
        exact (((monomorphisms MarkedSSet).inverseImage markedFaceNerve).arrow_mk_iso_iff
          (eqToIso e)).1 (mono_faceNerve_map_sphereInclusion U)
      · rintro _ _ _ ⟨a, h⟩
        have hn := (MarkedPresheaf.yonedaCompExtendIso markedFaceNerveSite).hom.naturality
          (MarkedSite.toSelf (MarkedSite.marked a h))
        rw [Functor.comp_map] at hn
        have : Mono (markedFaceNerveSite.map (MarkedSite.toSelf (MarkedSite.marked a h))) :=
          (MarkedPresheaf.mono_iff _).2 ⟨fun _ _ hgh => hgh⟩
        have hm : Mono ((MarkedPresheaf.extend markedFaceNerveSite).map
            ((MarkedPresheaf.yoneda atomMarking).map (MarkedSite.toSelf (MarkedSite.marked a h))) ≫
            (MarkedPresheaf.yonedaCompExtendIso markedFaceNerveSite).hom.app _) := by
          rw [hn]
          infer_instance
        exact @mono_of_mono _ _ _ _ _ (markedFaceNerve.map _) _ hm
    exact hle f (hI ▸ hf)

private theorem preservesMonomorphisms_flat :
    (MarkedPresheaf.flat.{u} atomMarking).PreservesMonomorphisms :=
  ⟨fun _ hf => (MarkedPresheaf.mono_iff _).2 hf⟩

instance preservesMonomorphisms_faceNerve : faceNerve.{u}.PreservesMonomorphisms :=
  have := preservesMonomorphisms_flat
  inferInstanceAs (MarkedPresheaf.flat atomMarking ⋙ markedFaceNerve).PreservesMonomorphisms

def grayProductRDC (P Q : RDCpx.{0}) : RDCpx.{0} :=
  ⟨⟨grayProduct P.obj.toOGP Q.obj.toOGP, isRDC_grayProduct P.obj.isRDC Q.obj.isRDC⟩⟩

private theorem boundary_closure_grayProductRDC (P Q : RDCpx.{0})
    (x : (grayProductRDC P Q).obj.toOGP) :
    (grayProductRDC P Q).obj.toOGP.boundary (.Iic x) 0 true =
      P.obj.toOGP.boundary (.Iic x.1) 0 true ×ˢ Q.obj.toOGP.boundary (.Iic x.2) 0 true := by
  refine SetLike.ext fun z => (mem_boundary_Iic_grayProduct P.obj.isRDC Q.obj.isRDC x.1 x.2 0 true
    z.1 z.2).trans ⟨?_, fun h => ⟨0, le_rfl, h.1, h.2⟩⟩
  rintro ⟨k, hk, hb, hy⟩
  obtain rfl := Nat.le_zero.1 hk
  exact ⟨hb, hy⟩

private theorem boundary_closure_grayProductRDC_eq_iff {P Q : RDCpx.{0}}
    {x y : (grayProductRDC P Q).obj.toOGP} :
    (grayProductRDC P Q).obj.toOGP.boundary (.Iic x) 0 true =
        (grayProductRDC P Q).obj.toOGP.boundary (.Iic y) 0 true ↔
      P.obj.toOGP.boundary (.Iic x.1) 0 true = P.obj.toOGP.boundary (.Iic y.1) 0 true ∧
        Q.obj.toOGP.boundary (.Iic x.2) 0 true = Q.obj.toOGP.boundary (.Iic y.2) 0 true := by
  rw [boundary_closure_grayProductRDC, boundary_closure_grayProductRDC]
  refine ⟨fun h => ?_, fun ⟨h1, h2⟩ => by rw [h1, h2]⟩
  obtain ⟨h1, h2⟩ := (Set.prod_eq_prod_iff_of_nonempty
    ((((P.obj.isRDC x.1).boundary 0 true).nonempty).prod
      ((Q.obj.isRDC x.2).boundary 0 true).nonempty)).1
    (congrArg (fun S : LowerSet (P.obj.toOGP × Q.obj.toOGP) =>
      (S : Set (P.obj.toOGP × Q.obj.toOGP))) h)
  exact ⟨SetLike.coe_injective h1, SetLike.coe_injective h2⟩

private noncomputable def rdcFaceNerveHomMk {P Q : RDCpx.{0}} (f : P.obj.toOGP →o Q.obj.toOGP)
    (hf : ∀ x y, P.obj.toOGP.boundary (.Iic x) 0 true = P.obj.toOGP.boundary (.Iic y) 0 true →
      Q.obj.toOGP.boundary (.Iic (f x)) 0 true = Q.obj.toOGP.boundary (.Iic (f y)) 0 true) :
    rdcFaceNerve.{u}.obj P ⟶ rdcFaceNerve.obj Q :=
  MarkedPresheaf.homMk (nerveMap (Monotone.functor (f := ULift.map f) fun _ _ h => f.monotone h))
    fun n _ he => (MarkedPresheaf.mem_marked_ofMarking _ _ n _).2
      (((MarkedPresheaf.mem_marked_ofMarking _ _ n _).1 he).imp_right
        (Or.imp (hf _ _) fun h => absurd h.1 (Set.notMem_empty _)))

private noncomputable def grayProductFst (P Q : RDCpx.{0}) :
    rdcFaceNerve.{u}.obj (grayProductRDC P Q) ⟶ rdcFaceNerve.obj P :=
  rdcFaceNerveHomMk OrderHom.fst fun _ _ h => (boundary_closure_grayProductRDC_eq_iff.1 h).1

private noncomputable def grayProductSnd (P Q : RDCpx.{0}) :
    rdcFaceNerve.{u}.obj (grayProductRDC P Q) ⟶ rdcFaceNerve.obj Q :=
  rdcFaceNerveHomMk OrderHom.snd fun _ _ h => (boundary_closure_grayProductRDC_eq_iff.1 h).2

private def pairChain {P Q : RDCpx.{0}} {n : SimplexCategoryᵒᵖ}
    (σ : (nerve (ULift.{u} P.obj.toOGP)).obj n) (τ : (nerve (ULift.{u} Q.obj.toOGP)).obj n) :
    (nerve (ULift.{u} (grayProductRDC P Q).obj.toOGP)).obj n :=
  Monotone.functor
    (f := fun i => ULift.up (((σ.obj i).down, (τ.obj i).down) : P.obj.toOGP × Q.obj.toOGP))
    fun _ _ h => ⟨ULift.down_le.2 (leOfHom (σ.map (homOfLE h))),
      ULift.down_le.2 (leOfHom (τ.map (homOfLE h)))⟩

private noncomputable def grayProductLift {P Q : RDCpx.{0}} {T : MarkedSSet}
    (u : T ⟶ rdcFaceNerve.{u}.obj P) (v : T ⟶ rdcFaceNerve.obj Q) :
    T ⟶ rdcFaceNerve.obj (grayProductRDC P Q) :=
  MarkedPresheaf.homMk
    { app n := ↾fun z => pairChain ((MarkedPresheaf.forget.map u).app n z)
        ((MarkedPresheaf.forget.map v).app n z)
      naturality n m f := by
        ext z
        exact (congrArg₂ (pairChain (P := P) (Q := Q))
          (NatTrans.naturality_apply (MarkedPresheaf.forget.map u) f z)
          (NatTrans.naturality_apply (MarkedPresheaf.forget.map v) f z)).trans rfl }
    fun n z hz => by
      obtain ⟨hn, hu | ⟨hM, -⟩⟩ := (MarkedPresheaf.mem_marked_ofMarking _ _ n _).1
        (MarkedPresheaf.map_mem_marked u hz)
      · obtain ⟨-, hv | ⟨hM, -⟩⟩ := (MarkedPresheaf.mem_marked_ofMarking _ _ n _).1
          (MarkedPresheaf.map_mem_marked v hz)
        · exact (MarkedPresheaf.mem_marked_ofMarking _ _ n _).2
            ⟨hn, Or.inl (boundary_closure_grayProductRDC_eq_iff.2 ⟨hu, hv⟩)⟩
        · exact absurd hM (Set.notMem_empty _)
      · exact absurd hM (Set.notMem_empty _)

private noncomputable def isLimitGrayProductFan (P Q : RDCpx.{0}) :
    IsLimit (BinaryFan.mk (grayProductFst.{u} P Q) (grayProductSnd P Q)) :=
  BinaryFan.IsLimit.mk _ grayProductLift
    (fun _ _ => MarkedPresheaf.hom_ext rfl) (fun _ _ => MarkedPresheaf.hom_ext rfl)
    fun {T} u v m hu hv => MarkedPresheaf.hom_ext (by
      ext n z
      refine nerve.ext_of_isThin (funext fun i => ULift.ext _ _ (Prod.ext ?_ ?_))
      · exact congrArg (fun φ : T ⟶ rdcFaceNerve.obj P =>
          (((MarkedPresheaf.forget.map φ).app n z).obj i).down) hu
      · exact congrArg (fun φ : T ⟶ rdcFaceNerve.obj Q =>
          (((MarkedPresheaf.forget.map φ).app n z).obj i).down) hv)

noncomputable def rdcFaceNerveGrayProductIso (P Q : RDCpx.{0}) :
    rdcFaceNerve.{u}.obj (grayProductRDC P Q) ≅ rdcFaceNerve.obj P ⨯ rdcFaceNerve.obj Q :=
  (isLimitGrayProductFan P Q).conePointUniqueUpToIso (limit.isLimit _)

theorem forget_map_rdcFaceNerveGrayProductIso_hom_fst (P Q : RDCpx.{0}) :
    MarkedPresheaf.forget.map ((rdcFaceNerveGrayProductIso.{u} P Q).hom ≫ prod.fst) =
      nerveMap (Monotone.functor (X := ULift.{u} (grayProductRDC P Q).obj.toOGP)
        (f := ULift.map fun x : P.obj.toOGP × Q.obj.toOGP ↦ x.1) fun _ _ h => monotone_fst h) :=
  congrArg MarkedPresheaf.forget.map (IsLimit.conePointUniqueUpToIso_hom_comp
    (isLimitGrayProductFan.{u} P Q) (limit.isLimit _) ⟨WalkingPair.left⟩)

theorem forget_map_rdcFaceNerveGrayProductIso_hom_snd (P Q : RDCpx.{0}) :
    MarkedPresheaf.forget.map ((rdcFaceNerveGrayProductIso.{u} P Q).hom ≫ prod.snd) =
      nerveMap (Monotone.functor (X := ULift.{u} (grayProductRDC P Q).obj.toOGP)
        (f := ULift.map fun x : P.obj.toOGP × Q.obj.toOGP ↦ x.2) fun _ _ h => monotone_snd h) :=
  congrArg MarkedPresheaf.forget.map (IsLimit.conePointUniqueUpToIso_hom_comp
    (isLimitGrayProductFan.{u} P Q) (limit.isLimit _) ⟨WalkingPair.right⟩)

end Atoms.Diagrammatic
