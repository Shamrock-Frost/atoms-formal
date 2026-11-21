import Atoms.Homotopical.Marked.Cellular

open CategoryTheory Limits Opposite

namespace Atoms.Homotopical

universe w v

variable {A B : Type v} [SmallCategory A] [SmallCategory B]

namespace MarkingData

variable (D : MarkingData A) (D' : MarkingData B) in
structure PreservesMarking (F : A ⥤ B) : Prop where
  markable (a : A) : D.markable a → D'.markable (F.obj a)
  degenerate {a b : A} (g : a ⟶ b) : D.degeneracy g → D'.Degenerate (F.map g)

variable {D : MarkingData A} {D' : MarkingData B} {F : A ⥤ B}

theorem PreservesMarking.map_degenerate (hF : PreservesMarking D D' F) {a b : A} {g : a ⟶ b}
    (hg : D.Degenerate g) : D'.Degenerate (F.map g) := by
  obtain ⟨c, p, q, hp, rfl⟩ := hg
  rw [F.map_comp]
  exact (hF.degenerate p hp).comp _

end MarkingData

variable {D : MarkingData A} {D' : MarkingData B} {F : A ⥤ B}
  (hF : MarkingData.PreservesMarking D D' F)

namespace MarkedSite

def map : MarkedSite D ⥤ MarkedSite D' where
  obj x := ⟨F.obj x.obj, x.isMarked, fun h => hF.markable _ (x.markable h)⟩
  map g := ⟨F.map g.1, fun h => (g.2 h).imp (fun ⟨hy, _⟩ => ⟨hy, inferInstance⟩)
    hF.map_degenerate⟩
  map_id _ := hom_ext (F.map_id _)
  map_comp _ _ := hom_ext (F.map_comp _ _)

@[simp]
theorem map_map_val {x y : MarkedSite D} (g : x ⟶ y) : ((map hF).map g).1 = F.map g.1 := rfl

theorem map_toSelf (x : MarkedSite D) : (map hF).map (toSelf x) = toSelf ((map hF).obj x) :=
  hom_ext (F.map_id _)

end MarkedSite

namespace MarkedPresheaf

open MarkedSite

instance epi_map_comp_yoneda_map_toSelf (x : MarkedSite D) :
    Epi ((map hF ⋙ MarkedPresheaf.yoneda.{w} D').map (toSelf x)) := by
  rw [Functor.comp_map, map_toSelf]
  exact epi_yoneda_map_toSelf _

noncomputable def extendAlong : MarkedPresheaf.{w} D ⥤ MarkedPresheaf.{w} D' :=
  extend (map hF ⋙ MarkedPresheaf.yoneda.{w} D')

def restrictAlong : MarkedPresheaf.{w} D' ⥤ MarkedPresheaf.{w} D :=
  nerve (map hF ⋙ MarkedPresheaf.yoneda.{w} D') inferInstance

noncomputable def extendAlongAdjunction : extendAlong.{w} hF ⊣ restrictAlong.{w} hF :=
  extendAdjunction _ _

def restrictAlongCompιIso : restrictAlong.{w} hF ⋙ ObjectProperty.ι _ ≅
    ObjectProperty.ι _ ⋙ (Functor.whiskeringLeft _ _ _).obj (map hF).op :=
  NatIso.ofComponents (fun Y => NatIso.ofComponents (fun x =>
    Equiv.toIso ((ObjectProperty.fullyFaithfulι _).homEquiv.trans uliftYonedaEquiv))
      fun {x x'} g => by
        ext f
        exact (uliftYonedaEquiv_naturality f.hom ((map hF).op.map g)).symm)
    fun {Y Y'} φ => by
      ext x f
      exact uliftYonedaEquiv_comp f.hom φ.hom

def restrictAlongCompForgetIso : restrictAlong.{w} hF ⋙ forget ≅
    forget ⋙ (Functor.whiskeringLeft _ _ _).obj F.op :=
  NatIso.ofComponents (fun Y => NatIso.ofComponents
      (fun a => ((restrictAlongCompιIso hF).app Y).app (op ((unmarked D).obj a.unop)))
      fun g => ((restrictAlongCompιIso hF).app Y).hom.naturality ((unmarked D).map g.unop).op)
    fun φ => by
      ext a : 2
      exact NatTrans.congr_app ((restrictAlongCompιIso hF).hom.naturality φ)
        (op ((unmarked D).obj a.unop))

theorem mem_marked_restrictAlong_iff (Y : MarkedPresheaf.{w} D') (a : A)
    (x : ((restrictAlong.{w} hF).obj Y).underlying.obj (op a)) :
    x ∈ ((restrictAlong hF).obj Y).marked a ↔
      D.markable a ∧
        ((restrictAlongCompForgetIso hF).app Y).hom.app (op a) x ∈ Y.marked (F.obj a) := by
  have he {x y : MarkedSite D} (g : x ⟶ y)
      (s : (MarkedPresheaf.yoneda D').obj ((map hF).obj y) ⟶ Y) :
      uliftYonedaEquiv ((MarkedPresheaf.yoneda D').map ((map hF).map g) ≫ s).hom =
        Y.obj.map ((map hF).map g).op (uliftYonedaEquiv s.hom) :=
    (uliftYonedaEquiv_naturality s.hom ((map hF).map g).op).symm
  constructor
  · rintro ⟨h, y, rfl⟩
    refine ⟨h, hF.markable a h, uliftYonedaEquiv y.hom, ?_⟩
    refine Eq.trans ?_ (he (toSelf (MarkedSite.marked a h)) y).symm
    exact congrArg (fun g => Y.obj.map (Quiver.Hom.op g) (uliftYonedaEquiv y.hom))
      (map_toSelf hF (MarkedSite.marked a h)).symm
  · rintro ⟨h, h', y, hy⟩
    refine ⟨h, ObjectProperty.homMk (uliftYonedaEquiv.symm y), ?_⟩
    refine ObjectProperty.hom_ext _ (uliftYonedaEquiv.injective ((he _ _).trans ?_))
    refine Eq.trans ?_ hy
    exact (congrArg (Y.obj.map ((map hF).map (toSelf (MarkedSite.marked a h))).op)
      (uliftYonedaEquiv.apply_symm_apply y)).trans
        (congrArg (fun g => Y.obj.map (Quiver.Hom.op g) y) (map_toSelf hF (MarkedSite.marked a h)))

private noncomputable def isoMk {X Y : MarkedPresheaf.{w} D} (e : X.underlying ≅ Y.underlying)
    (he : ∀ (a : A) (x : X.underlying.obj (op a)),
      x ∈ X.marked a ↔ e.hom.app (op a) x ∈ Y.marked a) :
    X ≅ Y where
  hom := homMk e.hom fun a x => (he a x).1
  inv := homMk e.inv fun a y hy => (he a _).2 (by rwa [e.inv_hom_id_app_apply])
  hom_inv_id := hom_ext ((forget.map_comp _ _).trans (e.hom_inv_id.trans (forget.map_id X).symm))
  inv_hom_id := hom_ext ((forget.map_comp _ _).trans (e.inv_hom_id.trans (forget.map_id Y).symm))

noncomputable def sharpCompRestrictAlongIso : sharp D' ⋙ restrictAlong.{w} hF ≅
    (Functor.whiskeringLeft _ _ _).obj F.op ⋙ sharp D :=
  NatIso.ofComponents (fun P => isoMk ((restrictAlongCompForgetIso hF).app ((sharp D').obj P))
      fun a x => (mem_marked_restrictAlong_iff hF _ a x).trans <|
        (and_iff_left_of_imp fun h => (mem_marked_sharp D' P _ _).2 (hF.markable a h)).trans
          (mem_marked_sharp D _ a _).symm)
    fun f => hom_ext ((restrictAlongCompForgetIso hF).hom.naturality ((sharp D').map f))

variable {L : (Aᵒᵖ ⥤ Type (max w v)) ⥤ Bᵒᵖ ⥤ Type (max w v)}
  (adj : L ⊣ (Functor.whiskeringLeft _ _ _).obj F.op)

noncomputable def extendAlongCompForgetIso : extendAlong.{w} hF ⋙ forget ≅ forget ⋙ L :=
  (((extendAlongAdjunction hF).comp (forgetSharpAdjunction D')).ofNatIsoRight
    (sharpCompRestrictAlongIso hF)).leftAdjointUniq ((forgetSharpAdjunction D).comp adj)

noncomputable def flatCompExtendAlongIso : flat D ⋙ extendAlong.{w} hF ≅ L ⋙ flat D' :=
  (((flatForgetAdjunction D).comp (extendAlongAdjunction hF)).ofNatIsoRight
    (restrictAlongCompForgetIso hF)).leftAdjointUniq (adj.comp (flatForgetAdjunction D'))

theorem preservesMonomorphisms_extendAlong (adj : L ⊣ (Functor.whiskeringLeft _ _ _).obj F.op)
    [L.PreservesMonomorphisms] :
    (extendAlong.{w} hF).PreservesMonomorphisms where
  preserves {X Y} f hf := by
    have := (mono_iff f).1 hf
    have h := (extendAlongCompForgetIso hF adj).hom.naturality f
    have : Mono ((extendAlong hF ⋙ forget).map f ≫
        (extendAlongCompForgetIso hF adj).hom.app Y) := by
      rw [h]
      infer_instance
    exact (mono_iff _).2 (@mono_of_mono _ _ _ _ _ _ _ this)

end MarkedPresheaf

end Atoms.Homotopical
