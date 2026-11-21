import Atoms.Homotopical.Simplicial.KanProduct

open CategoryTheory Limits MorphismProperty Simplicial MonoidalCategory Opposite

namespace Atoms.Homotopical

universe w v

variable {A : Type v} [SmallCategory A]

local notation "pr₁⋆" => Functor.obj (Functor.whiskeringLeft _ _ (Type _))
  (Functor.op (CategoryTheory.Prod.fst A SimplexCategory))

local notation "pr₂⋆" => Functor.obj (Functor.whiskeringLeft _ _ (Type _))
  (Functor.op (CategoryTheory.Prod.snd A SimplexCategory))

section ExternalProduct

abbrev extProd (X : Aᵒᵖ ⥤ Type (max w v)) (Y : SSet.{max w v}) :
    (A × SimplexCategory)ᵒᵖ ⥤ Type (max w v) :=
  pr₁⋆.obj X ⊗ pr₂⋆.obj Y

abbrev prodSSet (T : (A × SimplexCategory)ᵒᵖ ⥤ Type (max w v)) (Y : SSet.{max w v}) :
    (A × SimplexCategory)ᵒᵖ ⥤ Type (max w v) :=
  T ⊗ pr₂⋆.obj Y

abbrev extProdMap {X X' : Aᵒᵖ ⥤ Type (max w v)} {Y Y' : SSet.{max w v}} (f : X ⟶ X')
    (g : Y ⟶ Y') : extProd X Y ⟶ extProd X' Y' :=
  pr₁⋆.map f ⊗ₘ pr₂⋆.map g

abbrev prodSSetMap {T T' : (A × SimplexCategory)ᵒᵖ ⥤ Type (max w v)} {Y Y' : SSet.{max w v}}
    (f : T ⟶ T') (g : Y ⟶ Y') : prodSSet T Y ⟶ prodSSet T' Y' :=
  f ⊗ₘ pr₂⋆.map g

abbrev prodSSetFst (T : (A × SimplexCategory)ᵒᵖ ⥤ Type (max w v)) (Y : SSet.{max w v}) :
    prodSSet T Y ⟶ T :=
  CartesianMonoidalCategory.fst _ _

end ExternalProduct

theorem IsMonoSaturatedClass.comp_obj {B : Type v} [SmallCategory B]
    {P : (Bᵒᵖ ⥤ Type (max w v)) → Prop} (hP : IsMonoSaturatedClass P)
    (G : SSet.{max w v} ⥤ Bᵒᵖ ⥤ Type (max w v)) [PreservesColimitsOfSize.{max w v, max w v} G]
    (hG : ∀ {X Y : SSet.{max w v}} (f : X ⟶ Y), Mono f → Mono (G.map f)) :
    IsMonoSaturatedClass (fun Y ↦ P (G.obj Y)) where
  of_isPushout h hf h₀ h₁ h₂ :=
    have := preservesSmallestColimits_of_preservesColimits G
    hP.of_isPushout (G.map_isPushout h) (hG _ hf) h₀ h₁ h₂
  of_isColimit J _ _ F hF _ hc hPF :=
    hP.of_isColimit J (F ⋙ G) (fun i j h ↦ hG _ (hF i j h)) (isColimitOfPreserves G hc) hPF

section Boxes

abbrev boundaryProd (n : ℕ) :
    tensorRight (pr₂⋆.obj (∂Δ[n] : SSet.{max w v})) ⟶ tensorRight (pr₂⋆.obj Δ[n]) :=
  (tensoringRight ((A × SimplexCategory)ᵒᵖ ⥤ Type (max w v))).map (pr₂⋆.map ∂Δ[n].ι)

def extProdBoxes (M : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))) :
    MorphismProperty ((A × SimplexCategory)ᵒᵖ ⥤ Type (max w v)) :=
  fun _ _ f ↦ ∃ (K L : Aᵒᵖ ⥤ Type (max w v)) (t : K ⟶ L) (n : ℕ), M t ∧
    Nonempty (Arrow.mk f ≅ Arrow.mk (NatTrans.leibnizBox (boundaryProd n) (pr₁⋆.map t)))

private def extProdUnion {L : Aᵒᵖ ⥤ Type (max w v)} (K : Subfunctor L) (n : ℕ) :
    Subfunctor (extProd L Δ[n]) where
  obj c := {p | p.1 ∈ K.obj (op c.unop.1) ∨ p.2 ∈ (∂Δ[n]).obj (op c.unop.2)}
  map g _ hp := hp.imp (fun h ↦ K.map g.unop.1.op h) (fun h ↦ (∂Δ[n]).map g.unop.2.op h)

private theorem mem_extProdUnion_iff {L : Aᵒᵖ ⥤ Type (max w v)} (K : Subfunctor L) (n : ℕ)
    {c : (A × SimplexCategory)ᵒᵖ} (p : (extProd L Δ[n]).obj c) :
    p ∈ (extProdUnion K n).obj c ↔ p.1 ∈ K.obj (op c.unop.1) ∨ p.2 ∈ (∂Δ[n]).obj (op c.unop.2) :=
  Iff.rfl

private theorem isPushout_extProdUnion {L : Aᵒᵖ ⥤ Type (max w v)} (K : Subfunctor L) (n : ℕ) :
    IsPushout ((boundaryProd n).app (pr₁⋆.obj K.toFunctor))
      ((tensorRight (pr₂⋆.obj (∂Δ[n] : SSet.{max w v}))).map (pr₁⋆.map K.ι))
      (Subfunctor.lift (pr₁⋆.map K.ι ▷ pr₂⋆.obj Δ[n]) (fun _ _ ⟨⟨⟨_, hy⟩, _⟩, h⟩ ↦
        h ▸ (mem_extProdUnion_iff K n _).2 (Or.inl hy)) : _ ⟶ (extProdUnion K n).toFunctor)
      (Subfunctor.lift (pr₁⋆.obj L ◁ pr₂⋆.map ∂Δ[n].ι) (fun _ _ ⟨⟨_, ⟨_, hs⟩⟩, h⟩ ↦
        h ▸ (mem_extProdUnion_iff K n _).2 (Or.inr hs))) := by
  refine IsPushout.of_forall_isPushout_app fun c ↦ ?_
  refine Types.isPushout_of_isPullback_of_mono (k := (extProdUnion K n).ι.app c)
    (r' := (pr₁⋆.map K.ι ▷ pr₂⋆.obj Δ[n]).app c) (b' := (pr₁⋆.obj L ◁ pr₂⋆.map ∂Δ[n].ι).app c)
    ((CartesianMonoidalCategory.isPullback_whiskerRight_whiskerLeft (pr₁⋆.map K.ι)
      (pr₂⋆.map ∂Δ[n].ι)).flip.map ((evaluation _ _).obj c)) rfl rfl ?_ ?_
  · refine Set.eq_univ_of_forall fun ⟨⟨y, s⟩, hp⟩ ↦ ?_
    rcases (mem_extProdUnion_iff K n _).1 hp with hy | hs
    · exact Or.inl ⟨(⟨y, hy⟩, s), rfl⟩
    · exact Or.inr ⟨(y, ⟨s, hs⟩), rfl⟩
  · intro p q _ _ h
    exact (mono_iff_injective _).1 inferInstance h

private noncomputable def extProdUnionArrowIso {L : Aᵒᵖ ⥤ Type (max w v)} (K : Subfunctor L)
    (n : ℕ) : Arrow.mk (extProdUnion K n).ι ≅
      Arrow.mk (NatTrans.leibnizBox (boundaryProd n) (pr₁⋆.map K.ι)) :=
  Arrow.isoMk (isPushout_extProdUnion.{w, v} K n).isoPushout (Iso.refl _) (by
    refine (isPushout_extProdUnion.{w, v} K n).hom_ext ?_ ?_
    · simp only [Arrow.mk_hom, Arrow.mk_left, Arrow.mk_right, Iso.refl_hom, Category.comp_id]
      rw [← Category.assoc, IsPushout.inl_isoPushout_hom, NatTrans.inl_leibnizBox]
      rfl
    · simp only [Arrow.mk_hom, Arrow.mk_left, Arrow.mk_right, Iso.refl_hom, Category.comp_id]
      rw [← Category.assoc, IsPushout.inr_isoPushout_hom, NatTrans.inr_leibnizBox]
      rfl)

end Boxes

section Skeleton

variable (T : (A × SimplexCategory)ᵒᵖ ⥤ Type (max w v))

private abbrev level (n : ℕ) : Aᵒᵖ ⥤ Type (max w v) :=
  (Prod.sectL A (⦋n⦌ : SimplexCategory)).op ⋙ T

private def cellMap (n : ℕ) : extProd (level T n) Δ[n] ⟶ T where
  app c := TypeCat.ofHom fun p ↦
    T.map (Quiver.Hom.op ((𝟙 c.unop.1, SSet.stdSimplex.objEquiv p.2) :
      c.unop ⟶ (c.unop.1, ⦋n⦌))) p.1
  naturality c c' g := by
    ext ⟨y, s⟩
    change T.map _ (T.map _ y) = T.map g (T.map _ y)
    refine (T.map_comp_apply _ _ y).symm.trans (Eq.trans (congrArg (fun f ↦ T.map f y) ?_)
      (T.map_comp_apply _ _ y))
    apply Quiver.Hom.unop_inj
    exact Prod.hom_ext ((Category.id_comp _).trans (Category.comp_id _).symm) rfl

private theorem map_op_map_op {a a' a'' : A} {x x' x'' : SimplexCategory} (f : a' ⟶ a)
    (g : x' ⟶ x) (f' : a'' ⟶ a') (g' : x'' ⟶ x') (z : T.obj (op (a, x))) :
    T.map (Quiver.Hom.op ((f', g') : ((a'', x'') : A × SimplexCategory) ⟶ (a', x')))
      (T.map (Quiver.Hom.op ((f, g) : ((a', x') : A × SimplexCategory) ⟶ (a, x))) z) =
    T.map (Quiver.Hom.op ((f' ≫ f, g' ≫ g) : ((a'', x'') : A × SimplexCategory) ⟶ (a, x))) z :=
  (T.map_comp_apply _ _ z).symm

private def levelSub (S : Subfunctor T) (n : ℕ) : Subfunctor (level T n) where
  obj b := S.obj (op (b.unop, ⦋n⦌))
  map g _ hy := S.map ((Prod.sectL A (⦋n⦌ : SimplexCategory)).op.map g) hy

private theorem preimage_cellMap (S : Subfunctor T) (n : ℕ)
    (hS : ∀ m < n, Subfunctor.range (cellMap T m) ≤ S) :
    S.preimage (cellMap T n) = extProdUnion (levelSub T S n) n := by
  ext c ⟨y, s⟩
  induction c using Opposite.rec with | op c => ?_
  obtain ⟨b, ⟨d⟩⟩ := c
  constructor
  · intro h
    by_contra hc
    obtain ⟨hy, hs⟩ := not_or.1 hc
    have : Epi (SSet.stdSimplex.objEquiv s) := SimplexCategory.epi_iff_surjective.2 (not_not.1 hs)
    obtain ⟨⟨sec⟩⟩ := isSplitEpi_of_epi (SSet.stdSimplex.objEquiv s)
    refine hy ?_
    have e : T.map (Quiver.Hom.op ((𝟙 b, sec.section_) :
        ((b, ⦋n⦌) : A × SimplexCategory) ⟶ (b, ⦋d⦌))) ((cellMap T n).app (op (b, ⦋d⦌)) (y, s)) =
        y :=
      (map_op_map_op T (𝟙 b) (SSet.stdSimplex.objEquiv s) (𝟙 b) sec.section_ y).trans
        ((congrArg (fun f ↦ T.map (Quiver.Hom.op f) y)
          (Prod.hom_ext (Category.id_comp _) sec.id)).trans (T.map_id_apply _ y))
    have h' : T.map (Quiver.Hom.op ((𝟙 b, sec.section_) :
        ((b, ⦋n⦌) : A × SimplexCategory) ⟶ (b, ⦋d⦌))) ((cellMap T n).app (op (b, ⦋d⦌)) (y, s)) ∈
        S.obj (op (b, ⦋n⦌)) := S.map _ h
    rwa [e] at h'
  · rintro (hy | hs)
    · exact S.map _ hy
    · cases n with
      | zero => simp [SSet.boundary_zero] at hs
      | succ n =>
        obtain ⟨i, θ, hθ⟩ := SimplexCategory.eq_comp_δ_of_not_surjective _ hs
        refine hS n n.lt_succ_self _ ⟨(T.map (Quiver.Hom.op ((𝟙 b, SimplexCategory.δ i) :
          ((b, ⦋n⦌) : A × SimplexCategory) ⟶ (b, ⦋n + 1⦌))) y,
          SSet.stdSimplex.objEquiv.symm θ), ?_⟩
        change T.map _ (T.map _ y) = T.map _ y
        exact (map_op_map_op T _ _ _ _ y).trans (congrArg (fun f ↦ T.map (Quiver.Hom.op f) y)
          (Prod.hom_ext (Category.comp_id _) hθ.symm))

private theorem cellMap_injective_off (S : Subfunctor T) (n : ℕ)
    (hS : ∀ m < n, Subfunctor.range (cellMap T m) ≤ S) (c : (A × SimplexCategory)ᵒᵖ)
    (p q : (extProd (level T n) Δ[n]).obj c)
    (hp : p ∉ (extProdUnion (levelSub T S n) n).obj c)
    (hq : q ∉ (extProdUnion (levelSub T S n) n).obj c)
    (h : (cellMap T n).app c p = (cellMap T n).app c q) : p = q := by
  induction c using Opposite.rec with | op c => ?_
  obtain ⟨b, ⟨d⟩⟩ := c
  obtain ⟨y, s⟩ := p
  obtain ⟨y', s'⟩ := q
  obtain ⟨hy, hs⟩ := not_or.1 hp
  obtain ⟨hy', hs'⟩ := not_or.1 hq
  have : Epi (SSet.stdSimplex.objEquiv s) := SimplexCategory.epi_iff_surjective.2 (not_not.1 hs)
  let Y : SSet.{max w v} := (Prod.sectR b SimplexCategory).op ⋙ T
  have hnd : ∀ z, z ∉ (levelSub T S n).obj (op b) → z ∈ Y.nonDegenerate n := by
    rintro z hz ⟨m, hm, f, x, rfl⟩
    refine hz (hS m hm _ ⟨(x, SSet.stdSimplex.objEquiv.symm f), ?_⟩)
    rfl
  have e := Y.unique_nonDegenerate_simplex _ (SSet.stdSimplex.objEquiv s) ⟨y, hnd y hy⟩ rfl
    (SSet.stdSimplex.objEquiv s') ⟨y', hnd y' hy'⟩ h
  have e' := Y.unique_nonDegenerate_map _ (SSet.stdSimplex.objEquiv s) ⟨y, hnd y hy⟩ rfl
    (SSet.stdSimplex.objEquiv s') ⟨y', hnd y' hy'⟩ h
  obtain rfl : y = y' := congrArg Subtype.val e
  rw [SSet.stdSimplex.objEquiv.injective e']

variable {T} in
private theorem ι_mem_of_extProdUnion
    (W : MorphismProperty ((A × SimplexCategory)ᵒᵖ ⥤ Type (max w v))) [IsSaturated.{max w v} W]
    (hW : ∀ {L : Aᵒᵖ ⥤ Type (max w v)} (K : Subfunctor L) (n : ℕ), W (extProdUnion K n).ι)
    (X : Subfunctor T) : W X.ι := by
  let _ : SuccOrder (WithTop (ULift.{max w v} ℕ)) := SuccOrder.ofLinearWellFoundedLT _
  have hF : IsUnionChain X (fun z : ULift.{max w v} ℕ ↦ Subfunctor.range (cellMap T z.down))
      (fun j ↦ X ⊔ ⨆ (z : ULift.{max w v} ℕ) (_ : (z : WithTop (ULift.{max w v} ℕ)) < j),
        Subfunctor.range (cellMap T z.down)) := fun _ ↦ rfl
  refine hF.ι_mem (hF.top ?_) W fun z ↦ ?_
  · intro c x _
    induction c using Opposite.rec with | op c => ?_
    obtain ⟨b, ⟨d⟩⟩ := c
    simp only [Subfunctor.max_obj, Subfunctor.iSup_obj, Set.mem_union, Set.mem_iUnion,
      Subfunctor.range_obj, Set.mem_range]
    exact Or.inr ⟨⟨d⟩, (x, SSet.stdSimplex.objEquiv.symm (𝟙 _)), T.map_id_apply _ x⟩
  · have hS : ∀ m < z.down, Subfunctor.range (cellMap T m) ≤ _ := fun m hm ↦
      hF.le_of_lt (z := ⟨m⟩) (WithTop.coe_lt_coe.2 (ULift.up_lt.2 hm))
    exact MorphismProperty.of_isPushout (Subfunctor.isPushout_of_preimage _ (cellMap T z.down)
      (preimage_cellMap T _ z.down hS) (hF.succ z).symm
      (cellMap_injective_off T _ z.down hS)).flip (hW _ z.down)

end Skeleton

section Generation

variable (M : MorphismProperty (Aᵒᵖ ⥤ Type (max w v)))

private theorem leibnizBox_mem_saturation
    (hM : saturation.{max w v} M = MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)))
    {K L : Aᵒᵖ ⥤ Type (max w v)} (t : K ⟶ L) [Mono t] (n : ℕ) :
    saturation.{max w v} (extProdBoxes M)
      (NatTrans.leibnizBox (boundaryProd n) (pr₁⋆.map t)) := by
  have := NatTrans.isSaturated_leibnizPreimage.{max w v} (boundaryProd n)
    (saturation.{max w v} (extProdBoxes M))
  have hle : M ≤ (NatTrans.leibnizPreimage (boundaryProd n)
      (saturation.{max w v} (extProdBoxes M))).inverseImage pr₁⋆ :=
    fun K L t ht ↦ le_saturation _ _ ⟨K, L, t, n, ht, ⟨Iso.refl _⟩⟩
  have ht : saturation.{max w v} M t := by
    rw [hM]
    exact (inferInstance : Mono t)
  exact saturation_le _ _ hle t ht

theorem saturation_extProdBoxes
    (hM : saturation.{max w v} M = MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v))) :
    saturation.{max w v} (extProdBoxes M) =
      MorphismProperty.monomorphisms ((A × SimplexCategory)ᵒᵖ ⥤ Type (max w v)) := by
  refine le_antisymm (saturation_le _ _ ?_) fun T T' f (hf : Mono f) ↦ ?_
  · rintro _ _ f ⟨K, L, t, n, ht, ⟨e⟩⟩
    have : Mono t := (hM ▸ le_saturation.{max w v} _ _ ht : MorphismProperty.monomorphisms _ t)
    refine ((MorphismProperty.monomorphisms _).arrow_mk_iso_iff (e ≪≫
      (NatTrans.leibnizArrow (boundaryProd.{w, v} n)).mapIso (pr₁⋆.mapArrow.mapIso
        (Subfunctor.arrowIsoOfRangeEq t _ rfl)) ≪≫ (extProdUnionArrowIso.{w, v} _ n).symm)).2 ?_
    exact (inferInstance : Mono (extProdUnion.{w, v} (Subfunctor.range t) n).ι)
  · rw [← Subfunctor.toRange_ι f]
    refine MorphismProperty.comp_mem _ _ _
      (isomorphisms_le_of_containsIdentities _ _ (MorphismProperty.isomorphisms.infer_property _))
      (ι_mem_of_extProdUnion _ (fun K n ↦ ?_) _)
    exact ((saturation.{max w v} (extProdBoxes M)).arrow_mk_iso_iff
      (extProdUnionArrowIso K n)).2 (leibnizBox_mem_saturation M hM K.ι n)

end Generation

section Induction

variable {P : ((A × SimplexCategory)ᵒᵖ ⥤ Type (max w v)) → Prop}

private theorem extProd_mem_of_stdSimplex (hP : IsMonoSaturatedClass P)
    (hretract : ∀ {X Y} (i : X ⟶ Y) (r : Y ⟶ X), i ≫ r = 𝟙 X → P Y → P X)
    (X : Aᵒᵖ ⥤ Type (max w v)) (hX : ∀ n : ℕ, P (extProd X Δ[n])) (Y : SSet.{max w v}) :
    P (extProd X Y) :=
  let G := pr₂⋆ ⋙ tensorLeft (pr₁⋆.obj X)
  forall_of_stdSimplex (P := fun Y ↦ P (G.obj Y)) (hP.comp_obj G fun f _ ↦ inferInstance)
    (fun i r h ↦ hretract (G.map i) (G.map r) (by rw [← G.map_comp, h, G.map_id])) hX Y

theorem forall_of_extProd_stdSimplex (hP : IsMonoSaturatedClass P)
    (hretract : ∀ {X Y} (i : X ⟶ Y) (r : Y ⟶ X), i ≫ r = 𝟙 X → P Y → P X)
    (M : MorphismProperty (Aᵒᵖ ⥤ Type (max w v)))
    (hM : saturation.{max w v} M = MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)))
    (hgen : ∀ {K L} (t : K ⟶ L), M t → ∀ n : ℕ, P (extProd K Δ[n]) ∧ P (extProd L Δ[n]))
    (T : (A × SimplexCategory)ᵒᵖ ⥤ Type (max w v)) : P T := by
  refine forall_of_saturation_eq hP hretract _ (saturation_extProdBoxes M hM)
    (fun f ⟨K, L, t, n, ht, ⟨e⟩⟩ ↦ ⟨?_, ?_⟩) T
  · refine hP.of_iso (Comma.leftIso e).symm (hP.of_isPushout (IsPushout.of_hasPushout _ _)
      (inferInstanceAs (Mono (_ ◁ _))) ?_ ?_ ?_)
    · exact extProd_mem_of_stdSimplex hP hretract K (fun n ↦ (hgen t ht n).1) _
    · exact (hgen t ht n).1
    · exact extProd_mem_of_stdSimplex hP hretract L (fun n ↦ (hgen t ht n).2) _
  · exact hP.of_iso (Comma.rightIso e).symm (hgen t ht n).2

end Induction

section Localizer

private theorem extProdMap_id (X : Aᵒᵖ ⥤ Type (max w v)) {Y Y' : SSet.{max w v}} (h : Y ⟶ Y') :
    extProdMap (𝟙 X) h = pr₁⋆.obj X ◁ pr₂⋆.map h := by
  rw [extProdMap, CategoryTheory.Functor.map_id, id_tensorHom]

private instance isIso_prodSSetFst_terminal (T : (A × SimplexCategory)ᵒᵖ ⥤ Type (max w v)) :
    IsIso (CartesianMonoidalCategory.fst T (pr₂⋆.obj (⊤_ SSet.{max w v}))) :=
  let hU : IsTerminal (pr₂⋆.obj (⊤_ SSet.{max w v})) :=
    IsTerminal.isTerminalObj _ _ terminalIsTerminal
  ⟨CartesianMonoidalCategory.lift (𝟙 T) (hU.from T),
    CartesianMonoidalCategory.hom_ext _ _ (by simp) (hU.hom_ext _ _), by simp⟩

variable {B : Type v} [SmallCategory B] {V : MorphismProperty (Bᵒᵖ ⥤ Type (max w v))}
  [IsALocalizer V]

theorem IsALocalizer.app_mem_of_extProd
    (Φ Ψ : ((A × SimplexCategory)ᵒᵖ ⥤ Type (max w v)) ⥤ (Bᵒᵖ ⥤ Type (max w v)))
    [PreservesColimitsOfSize.{max w v, max w v} Φ] [PreservesColimitsOfSize.{max w v, max w v} Ψ]
    (hΦ : ∀ {X Y} (f : X ⟶ Y), Mono f → Mono (Φ.map f))
    (hΨ : ∀ {X Y} (f : X ⟶ Y), Mono f → Mono (Ψ.map f)) (α : Φ ⟶ Ψ)
    (M : MorphismProperty (Aᵒᵖ ⥤ Type (max w v)))
    (hM : saturation.{max w v} M = MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)))
    (hgen : ∀ {K L : Aᵒᵖ ⥤ Type (max w v)} (t : K ⟶ L), M t →
      ∀ n : ℕ, V (α.app (extProd K Δ[n])) ∧ V (α.app (extProd L Δ[n])))
    (T : (A × SimplexCategory)ᵒᵖ ⥤ Type (max w v)) : V (α.app T) :=
  forall_of_extProd_stdSimplex (IsALocalizer.isMonoSaturatedClass_app Φ Ψ hΦ hΨ α)
    (fun i r h hY ↦ V.of_retract
      { i := Arrow.homMk (Φ.map i) (Ψ.map i) (α.naturality i)
        r := Arrow.homMk (Φ.map r) (Ψ.map r) (α.naturality r)
        retract := by ext <;> simp [← Functor.map_comp, h] } hY) M hM hgen T

theorem IsALocalizer.map_prodSSet_map_mem_of_kanWeak
    (F : ((A × SimplexCategory)ᵒᵖ ⥤ Type (max w v)) ⥤ (Bᵒᵖ ⥤ Type (max w v)))
    [PreservesColimitsOfSize.{max w v, max w v} F]
    (hF : ∀ {X Y} (f : X ⟶ Y), Mono f → Mono (F.map f))
    (M : MorphismProperty (Aᵒᵖ ⥤ Type (max w v)))
    (hM : saturation.{max w v} M = MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)))
    (hproj : ∀ {K L : Aᵒᵖ ⥤ Type (max w v)} (t : K ⟶ L), M t → ∀ n : ℕ,
      V (F.map (extProdMap (𝟙 K) (terminal.from Δ[n]))) ∧
        V (F.map (extProdMap (𝟙 L) (terminal.from Δ[n]))))
    (T : (A × SimplexCategory)ᵒᵖ ⥤ Type (max w v)) {Y Z : SSet.{max w v}} (g : Y ⟶ Z)
    (hg : kanWeak g) : V (F.map (prodSSetMap (𝟙 T) g)) := by
  have key (X : Aᵒᵖ ⥤ Type (max w v))
      (hX : ∀ n : ℕ, V (F.map (extProdMap (𝟙 X) (terminal.from Δ[n])))) (n : ℕ) :
      V (F.map (extProd X Δ[n] ◁ pr₂⋆.map g)) := by
    let G := pr₂⋆ ⋙ tensorLeft (pr₁⋆.obj X) ⋙ F
    have hk : kanWeak (Δ[n] ◁ g) := (kanWeak.arrow_mk_iso_iff
      (Arrow.isoMk (β_ Δ[n] Y) (β_ Δ[n] Z) (BraidedCategory.braiding_naturality_right _ _).symm)).2
      (kanWeak_whiskerRight hg Δ[n])
    have : IsALocalizer.{max w v, v} V := ⟨IsALocalizer.hasTwoOutOfThreeProperty,
      IsALocalizer.rlp_monomorphisms_le, IsALocalizer.isStableUnderCobaseChange,
      IsALocalizer.isStableUnderTransfiniteComposition⟩
    have hG : V (F.map (pr₁⋆.obj X ◁ pr₂⋆.obj Δ[n] ◁ pr₂⋆.map g)) :=
      kanWeak_le_inverseImage.{max w v} G (fun _ _ f _ ↦ hF _ inferInstance) (V := V)
        (fun m ↦ (congrArg (fun φ ↦ V (F.map φ)) (extProdMap_id X (terminal.from Δ[m]))).mp
          (hX m)) _ hk
    refine (V.arrow_mk_iso_iff (Arrow.isoMk (F.mapIso (α_ _ _ _)) (F.mapIso (α_ _ _ _)) ?_)).2 hG
    simp [← Functor.map_comp]
  have e : prodSSetMap (𝟙 T) g = T ◁ pr₂⋆.map g := id_tensorHom _ _
  rw [e]
  exact IsALocalizer.app_mem_of_extProd (tensorRight (pr₂⋆.obj Y) ⋙ F)
    (tensorRight (pr₂⋆.obj Z) ⋙ F) (fun _ _ ↦ hF _ inferInstance) (fun _ _ ↦ hF _ inferInstance)
    (Functor.whiskerRight ((tensoringRight _).map (pr₂⋆.map g)) F) M hM
    (fun t ht n ↦ ⟨key _ (fun n ↦ (hproj t ht n).1) n, key _ (fun n ↦ (hproj t ht n).2) n⟩) T

end Localizer

section Projections

variable {V : MorphismProperty ((A × SimplexCategory)ᵒᵖ ⥤ Type (max w v))} [IsALocalizer V]

private theorem map_terminal_from_nerve_mem
    (G : SSet.{max w v} ⥤ (A × SimplexCategory)ᵒᵖ ⥤ Type (max w v)) (C : Type (max w v))
    [SmallCategory C] [HasTerminal C]
    (h : V (G.map ((simplicialCylinder.{max w v}.contraction).app (nerve C)))) :
    V (G.map (terminal.from (nerve C))) := by
  have he (ε : Bool) : V (G.map ((simplicialCylinder.{max w v}.endpoint ε).app (nerve C))) :=
    V.of_postcomp _ _ h ((congrArg (fun φ ↦ V φ) ((G.map_comp _ _).symm.trans
      ((congrArg G.map (simplicialCylinder.endpoint_app_contraction_app ε (nerve C))).trans
        (G.map_id _)))).mpr (V.id_mem _))
  have hc : V (G.map (nerveContraction C)) :=
    V.of_precomp _ _ (he false) ((congrArg (fun φ ↦ V φ) ((G.map_comp _ _).symm.trans
      ((congrArg G.map (endpoint_false_nerveContraction C)).trans (G.map_id _)))).mpr
        (V.id_mem _))
  have hps : V (G.map (terminal.from (nerve C) ≫ nerveTerminal C)) :=
    (congrArg (fun φ ↦ V φ) ((G.map_comp _ _).symm.trans
      (congrArg G.map (endpoint_true_nerveContraction C)))).mp (V.comp_mem _ _ (he true) hc)
  have hsp : nerveTerminal C ≫ terminal.from (nerve C) = 𝟙 _ := terminal.hom_ext _ _
  let ρ : RetractArrow (G.map (terminal.from (nerve C)))
      (G.map (terminal.from (nerve C) ≫ nerveTerminal C)) :=
    { i := Arrow.homMk (𝟙 _) (G.map (nerveTerminal C)) ((Category.id_comp _).trans (G.map_comp _ _))
      r := Arrow.homMk (𝟙 _) (G.map (terminal.from (nerve C))) ((Category.id_comp _).trans
        ((congrArg G.map (terminal.hom_ext _ _)).trans (G.map_comp _ _)))
      retract := Arrow.hom_ext _ _ (Category.id_comp _) ((G.map_comp _ _).symm.trans
        ((congrArg G.map hsp).trans (G.map_id _))) }
  exact V.of_retract ρ hps

private theorem whiskerLeft_terminal_from_mem (h : ∀ T, V (prodSSetFst T Δ[1]))
    (T : (A × SimplexCategory)ᵒᵖ ⥤ Type (max w v)) (m : ℕ) :
    V (T ◁ pr₂⋆.map (terminal.from Δ[m])) := by
  let G := pr₂⋆ ⋙ tensorLeft T
  let N := nerve (ULift.{max w v} (Fin (m + 1)))
  have hN : V (T ◁ CartesianMonoidalCategory.snd (pr₂⋆.obj Δ[1]) (pr₂⋆.obj N)) :=
    (V.arrow_mk_iso_iff (Arrow.isoMk (whiskerLeftIso T (β_ _ _) ≪≫ (α_ _ _ _).symm)
      (Iso.refl _) (CartesianMonoidalCategory.hom_ext _ _ (by simp [prodSSetFst])
        (by simp [prodSSetFst])))).2 (h (T ⊗ pr₂⋆.obj N))
  have h2 : V (G.map ((SSet.stdSimplex.isoNerve m).hom ≫ terminal.from N)) := by
    rw [G.map_comp]
    exact V.comp_mem _ _ (IsALocalizer.isomorphisms_le _ (isomorphisms.infer_property _))
      (map_terminal_from_nerve_mem G _ hN)
  rwa [terminal.hom_ext ((SSet.stdSimplex.isoNerve m).hom ≫ terminal.from N)
    (terminal.from Δ[m])] at h2

private theorem fst_stdSimplex_mem (h : ∀ T, V (prodSSetFst T Δ[1]))
    (T : (A × SimplexCategory)ᵒᵖ ⥤ Type (max w v)) (m : ℕ) :
    V (CartesianMonoidalCategory.fst T (pr₂⋆.obj Δ[m])) := by
  exact (congrArg (fun φ ↦ V φ) (CartesianMonoidalCategory.whiskerLeft_fst _ _)).mp
    (V.comp_mem _ _ (whiskerLeft_terminal_from_mem h T m) (IsALocalizer.isomorphisms_le _
      (isomorphisms.infer_property (CartesianMonoidalCategory.fst T (pr₂⋆.obj (⊤_ SSet))))))

theorem IsALocalizer.tfae_prodSSet (M : MorphismProperty (Aᵒᵖ ⥤ Type (max w v)))
    (hM : saturation.{max w v} M = MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v))) :
    List.TFAE
      [∀ T, V (prodSSetFst T Δ[1]),
        ∀ {K L : Aᵒᵖ ⥤ Type (max w v)} (t : K ⟶ L), M t → ∀ n : ℕ,
          V (extProdMap (𝟙 K) (terminal.from Δ[n])) ∧ V (extProdMap (𝟙 L) (terminal.from Δ[n])),
        ∀ (T : (A × SimplexCategory)ᵒᵖ ⥤ Type (max w v)) {Y Z : SSet.{max w v}} (g : Y ⟶ Z),
          kanWeak g → V (prodSSetMap (𝟙 T) g)] := by
  tfae_have 1 → 2 := fun h {K L} _ _ n ↦
    ⟨(congrArg (fun φ ↦ V φ) (extProdMap_id K _)).mpr (whiskerLeft_terminal_from_mem h _ n),
      (congrArg (fun φ ↦ V φ) (extProdMap_id L _)).mpr (whiskerLeft_terminal_from_mem h _ n)⟩
  tfae_have 2 → 3 := fun h T _ _ g hg ↦
    IsALocalizer.map_prodSSet_map_mem_of_kanWeak (𝟭 _) (fun _ hf ↦ hf) M hM h T g hg
  tfae_have 3 → 1 := fun h T ↦ by
    refine (congrArg (fun φ ↦ V φ) (CartesianMonoidalCategory.tensorHom_fst _ _)).mp
      (V.comp_mem _ _ (h T (terminal.from Δ[1]) (terminal_from_stdSimplex_mem_kanWeak 1))
        (IsALocalizer.isomorphisms_le _ (isomorphisms.infer_property
          (CartesianMonoidalCategory.fst T (pr₂⋆.obj (⊤_ SSet))))))
  tfae_finish

theorem IsALocalizer.prodSSetMap_mem (h : ∀ T, V (prodSSetFst T Δ[1]))
    {T T' : (A × SimplexCategory)ᵒᵖ ⥤ Type (max w v)} (f : T ⟶ T') (hf : V f)
    (Y : SSet.{max w v}) : V (prodSSetMap f (𝟙 Y)) := by
  have e : prodSSetMap f (𝟙 Y) = f ▷ pr₂⋆.obj Y := by
    rw [prodSSetMap, CategoryTheory.Functor.map_id, tensorHom_id]
  refine (congrArg (fun φ ↦ V φ) e).mpr (forall_of_stdSimplex (P := fun Y ↦ V (f ▷ pr₂⋆.obj Y))
    ((IsALocalizer.isMonoSaturatedClass_app (tensorLeft T) (tensorLeft T')
      (fun _ _ ↦ inferInstance) (fun _ _ ↦ inferInstance) ((tensoringLeft _).map f)).comp_obj pr₂⋆
        (fun _ _ ↦ inferInstance))
    (fun i r hir hY ↦ by
      have hw (U : (A × SimplexCategory)ᵒᵖ ⥤ Type (max w v)) :
          U ◁ pr₂⋆.map i ≫ U ◁ pr₂⋆.map r = 𝟙 _ := by
        rw [← MonoidalCategory.whiskerLeft_comp, ← CategoryTheory.Functor.map_comp, hir,
          CategoryTheory.Functor.map_id, MonoidalCategory.whiskerLeft_id]
      exact V.of_retract
        { i := Arrow.homMk (T ◁ pr₂⋆.map i) (T' ◁ pr₂⋆.map i) (whisker_exchange _ _)
          r := Arrow.homMk (T ◁ pr₂⋆.map r) (T' ◁ pr₂⋆.map r) (whisker_exchange _ _)
          retract := Arrow.hom_ext _ _ (hw T) (hw T') } hY)
    (fun m ↦ V.of_postcomp _ _ (fst_stdSimplex_mem h T' m)
      ((congrArg (fun φ ↦ V φ) (CartesianMonoidalCategory.whiskerRight_fst f _)).mpr
        (V.comp_mem _ _ (fst_stdSimplex_mem h T m) hf))) Y)

end Projections

end Atoms.Homotopical
