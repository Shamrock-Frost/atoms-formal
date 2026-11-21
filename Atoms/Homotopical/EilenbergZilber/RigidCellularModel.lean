import Atoms.Homotopical.Cellular.Model
import Atoms.Homotopical.EilenbergZilber.Lemma

open CategoryTheory Limits MorphismProperty Opposite

namespace Atoms.Homotopical

universe w v

namespace EZCategory

section Generators

variable (A : Type v) [SmallCategory A] [EZCategory A]

def boundaryInclusions : MorphismProperty (Aᵒᵖ ⥤ Type (max w v)) :=
  MorphismProperty.ofHoms fun a : A ↦ (uliftBoundary.{w} a).ι

omit [EZCategory A] in
theorem boundaryInclusions_le_monomorphisms :
    boundaryInclusions.{w} A ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)) := by
  rintro _ _ _ ⟨a⟩
  exact MorphismProperty.monomorphisms.infer_property _

end Generators

section Cells

variable {A : Type v} [SmallCategory A] {Y : Aᵒᵖ ⥤ Type (max w v)}

variable (R : Subfunctor Y)

structure NondegenerateCell : Type (max w v) where
  obj : A
  cell : Y.obj (op obj)
  isNondegenerate : IsNondegenerate Y cell
  not_mem : cell ∉ R.obj (op obj)

def cellSetoid : Setoid (NondegenerateCell R) where
  r z w := ∃ e : z.obj ≅ w.obj, Y.map e.hom.op w.cell = z.cell
  iseqv :=
    { refl z := ⟨Iso.refl _, by simp⟩
      symm := by
        rintro z w ⟨e, he⟩
        refine ⟨e.symm, ?_⟩
        rw [← he, Iso.symm_hom, ← Functor.map_comp_apply, ← op_comp, e.inv_hom_id, op_id,
          Functor.map_id_apply]
      trans := by
        rintro z w u ⟨e, he⟩ ⟨f, hf⟩
        refine ⟨e ≪≫ f, ?_⟩
        rw [Iso.trans_hom, op_comp, Functor.map_comp_apply, hf, he] }

def CellClass : Type (max w v) := Quotient (cellSetoid R)

variable {R}

noncomputable def rep (q : CellClass R) : NondegenerateCell R :=
  Quotient.out (s := cellSetoid R) q

def cellMk (z : NondegenerateCell R) : CellClass R := Quotient.mk (cellSetoid R) z

theorem cellMk_rep (q : CellClass R) : cellMk (rep q) = q :=
  Quotient.out_eq (s := cellSetoid R) q

theorem exists_iso_rep_cellMk (z : NondegenerateCell R) :
    ∃ e : (rep (cellMk z)).obj ≅ z.obj, Y.map e.hom.op z.cell = (rep (cellMk z)).cell :=
  Quotient.mk_out (s := cellSetoid R) z

theorem cellMk_eq_of_iso {z w : NondegenerateCell R} (e : z.obj ≅ w.obj)
    (h : Y.map e.hom.op w.cell = z.cell) : cellMk z = cellMk w :=
  Quotient.sound (s := cellSetoid R) ⟨e, h⟩

noncomputable def cellImage (q : CellClass R) : Subfunctor Y :=
  Subfunctor.range (uliftYonedaEquiv.symm (rep q).cell)

theorem mem_cellImage_iff (q : CellClass R) {b : Aᵒᵖ} (x : Y.obj b) :
    x ∈ (cellImage q).obj b ↔ ∃ g : b.unop ⟶ (rep q).obj, Y.map g.op (rep q).cell = x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.down, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨⟨g⟩, rfl⟩

theorem map_mem_cellImage_cellMk (z : NondegenerateCell R) {b : A} (g : b ⟶ z.obj) :
    Y.map g.op z.cell ∈ (cellImage (cellMk z)).obj (op b) := by
  obtain ⟨e, he⟩ := exists_iso_rep_cellMk z
  rw [mem_cellImage_iff]
  refine ⟨g ≫ e.inv, ?_⟩
  rw [← he, ← Functor.map_comp_apply, ← op_comp, Category.assoc, e.inv_hom_id,
    Category.comp_id]

variable [EZCategory A]

noncomputable def cellDeg (q : CellClass R) : ℕ := deg (rep q).obj

theorem cellDeg_cellMk (z : NondegenerateCell R) : cellDeg (cellMk z) = deg z.obj := by
  obtain ⟨e, -⟩ := exists_iso_rep_cellMk z
  exact deg_eq_of_iso e

variable (R)

def cellLT : CellClass R → CellClass R → Prop :=
  (Prod.Lex (· < ·) WellOrderingRel).onFun fun q : CellClass R ↦ (cellDeg q, q)

instance isWellOrder_cellLT : IsWellOrder (CellClass R) (cellLT R) :=
  Function.Injective.isWellOrder (f := fun q : CellClass R ↦ (cellDeg q, q))
    (Prod.Lex (· < ·) WellOrderingRel) fun _ _ h ↦ congrArg Prod.snd h

noncomputable instance : LinearOrder (CellClass R) :=
  IsWellOrder.linearOrder (cellLT R)

instance : WellFoundedLT (CellClass R) :=
  ⟨(isWellOrder_cellLT R).wf⟩

noncomputable instance : OrderBot (WithTop (CellClass R)) :=
  WellFoundedLT.toOrderBot _

noncomputable instance : SuccOrder (WithTop (CellClass R)) :=
  SuccOrder.ofLinearWellFoundedLT _

variable {R}

theorem lt_of_cellDeg_lt {q q' : CellClass R} (h : cellDeg q < cellDeg q') : q < q' :=
  Prod.Lex.left _ _ h

theorem cellDeg_le_of_lt {q q' : CellClass R} (h : q < q') : cellDeg q ≤ cellDeg q' :=
  not_lt.1 fun h' ↦ lt_asymm h (lt_of_cellDeg_lt h')

variable (R)

noncomputable def cellChain (j : WithTop (CellClass R)) : Subfunctor Y :=
  R ⊔ ⨆ (q : CellClass R) (_ : (q : WithTop (CellClass R)) < j), cellImage q

theorem isUnionChain_cellChain :
    IsUnionChain R (fun q : CellClass R ↦ cellImage q) (cellChain R) :=
  fun _ ↦ rfl

variable {R}

theorem map_mem_cellChain {c b : A} (w : Y.obj (op c)) (hw : IsNondegenerate Y w) (g : b ⟶ c)
    {j : WithTop (CellClass R)}
    (h : ∀ hR : w ∉ R.obj (op c), ((cellMk ⟨c, w, hw, hR⟩ : CellClass R) : WithTop _) < j) :
    Y.map g.op w ∈ (cellChain R j).obj (op b) := by
  by_cases hR : w ∈ R.obj (op c)
  · exact le_sup_left (a := R) (op b) (R.map g.op hR)
  · exact (isUnionChain_cellChain R).le_of_lt (h hR) (op b)
      (map_mem_cellImage_cellMk ⟨c, w, hw, hR⟩ g)

variable (R)

theorem cellChain_top : cellChain R ⊤ = ⊤ := by
  refine eq_top_iff.2 fun b x _ ↦ ?_
  obtain ⟨c, p, w, -, hw, rfl⟩ := exists_isNondegenerate Y b.unop x
  exact map_mem_cellChain w hw p fun _ ↦ WithTop.coe_lt_top _

variable {R}

theorem map_mem_cellChain_of_not_isSplitEpi (q : CellClass R) {b : A}
    (f : b ⟶ (rep q).obj) (hf : ¬IsSplitEpi f) :
    Y.map f.op (rep q).cell ∈ (cellChain R q).obj (op b) := by
  obtain ⟨c₁, p₁, i, hp₁, hi, rfl⟩ := exists_factorization f
  have hlt : deg c₁ < deg (rep q).obj := by
    refine lt_of_le_of_ne (deg_le_of_mono i hi) fun he ↦ hf ?_
    have := isIso_of_mono_of_deg_eq i hi he
    have := hp₁
    infer_instance
  obtain ⟨c, p₂, w, hp₂, hw, hpw⟩ := exists_isNondegenerate Y c₁ (Y.map i.op (rep q).cell)
  have := hp₂
  have hc : deg c < cellDeg q := (deg_le_of_isSplitEpi p₂).trans_lt hlt
  rw [op_comp, Functor.map_comp_apply, ← hpw, ← Functor.map_comp_apply, ← op_comp]
  exact map_mem_cellChain w hw _ fun _ ↦ WithTop.coe_lt_coe.2
    (lt_of_cellDeg_lt ((cellDeg_cellMk _).trans_lt hc))

theorem map_not_mem_cellChain_of_isSplitEpi (q : CellClass R) {b : A}
    (p : b ⟶ (rep q).obj) (hp : IsSplitEpi p) :
    Y.map p.op (rep q).cell ∉ (cellChain R q).obj (op b) := by
  intro h
  simp only [cellChain, Subfunctor.max_obj, Subfunctor.iSup_obj, Set.mem_union,
    Set.mem_iUnion, exists_prop] at h
  rcases h with h | ⟨q', hq', h⟩
  · apply (rep q).not_mem
    have := hp
    have h' : Y.map (section_ p).op (Y.map p.op (rep q).cell) ∈ R.obj (op (rep q).obj) :=
      R.map (section_ p).op h
    rwa [← Functor.map_comp_apply, ← op_comp, IsSplitEpi.id, op_id, Functor.map_id_apply] at h'
  · have hq' : q' < q := WithTop.coe_lt_coe.1 hq'
    obtain ⟨g, hg⟩ := (mem_cellImage_iff q' _).1 h
    obtain ⟨c₁, p₁, i, hp₁, hi, rfl⟩ := exists_factorization g
    obtain ⟨c, p₂, w, hp₂, hw, hpw⟩ := exists_isNondegenerate Y c₁ (Y.map i.op (rep q').cell)
    have hzw : Y.map p.op (rep q).cell = Y.map (p₁ ≫ p₂).op w := by
      rw [← hg]
      simp only [op_comp, Functor.map_comp_apply, ← hpw]
    have := hp₁
    have := hp₂
    obtain ⟨e, ⟨-, he⟩, -⟩ := existsUnique_iso_of_isNondegenerate Y p (p₁ ≫ p₂) _ w hp
      (rep q).isNondegenerate inferInstance hw hzw
    have h₁ : deg c ≤ deg c₁ := deg_le_of_isSplitEpi p₂
    have h₂ : deg c₁ ≤ deg (rep q').obj := deg_le_of_mono i hi
    have h₃ : deg (rep q').obj ≤ deg (rep q).obj := cellDeg_le_of_lt hq'
    have h₄ : deg (rep q).obj = deg c := deg_eq_of_iso e
    have := isIso_of_mono_of_deg_eq i hi (by omega)
    have := isIso_of_isSplitEpi_of_deg_eq p₂ (by omega)
    have hw' : Y.map (inv p₂ ≫ i).op (rep q').cell = w := by
      rw [op_comp, Functor.map_comp_apply, ← hpw, op_inv, Functor.map_hom_inv_apply]
    have hqq : q = q' := by
      rw [← cellMk_rep q, ← cellMk_rep q']
      refine cellMk_eq_of_iso (e ≪≫ asIso (inv p₂ ≫ i)) ?_
      rw [Iso.trans_hom, asIso_hom, op_comp (f := e.hom), Functor.map_comp_apply, hw', he]
    exact lt_irrefl _ (hqq ▸ hq')

theorem eq_of_map_eq_of_isSplitEpi_of_dominant (q : CellClass R)
    (hq : ∀ e : (rep q).obj ≅ (rep q).obj, Y.map e.hom.op (rep q).cell = (rep q).cell →
      e = Iso.refl _)
    {b : A} (p p' : b ⟶ (rep q).obj) (hp : IsSplitEpi p) (hp' : IsSplitEpi p')
    (h : Y.map p.op (rep q).cell = Y.map p'.op (rep q).cell) : p = p' := by
  obtain ⟨e, ⟨he, hec⟩, -⟩ := existsUnique_iso_of_isNondegenerate Y p p' _ _ hp
    (rep q).isNondegenerate hp' (rep q).isNondegenerate h
  rw [← he, hq e hec, Iso.refl_hom, Category.comp_id]

theorem eq_of_map_eq_of_isSplitEpi [HasTrivialAutomorphisms A] (q : CellClass R)
    {b : A} (p p' : b ⟶ (rep q).obj) (hp : IsSplitEpi p) (hp' : IsSplitEpi p')
    (h : Y.map p.op (rep q).cell = Y.map p'.op (rep q).cell) : p = p' :=
  eq_of_map_eq_of_isSplitEpi_of_dominant q (fun _ _ ↦ Subsingleton.elim _ _) p p' hp hp' h

theorem range_boundary_ι_comp_le_cellChain (q : CellClass R) :
    Subfunctor.range ((uliftBoundary.{w} (rep q).obj).ι ≫ uliftYonedaEquiv.symm (rep q).cell) ≤
      cellChain R q := by
  rintro b _ ⟨f, rfl⟩
  exact map_mem_cellChain_of_not_isSplitEpi q (b := b.unop) f.1.down f.2

theorem range_le_cellChain_succ (q : CellClass R) :
    Subfunctor.range (uliftYonedaEquiv.symm (rep q).cell) ≤
      cellChain R (Order.succ (q : WithTop (CellClass R))) :=
  (isUnionChain_cellChain R).le_of_lt
    (Order.lt_succ_of_not_isMax (not_isMax_of_lt (WithTop.coe_lt_top q)))

theorem isPushout_boundaryInclusion_of_dominant (q : CellClass R)
    (hq : ∀ e : (rep q).obj ≅ (rep q).obj, Y.map e.hom.op (rep q).cell = (rep q).cell →
      e = Iso.refl _) :
    IsPushout (Subfunctor.lift _ (range_boundary_ι_comp_le_cellChain q))
      (uliftBoundary.{w} (rep q).obj).ι
      (Subfunctor.homOfLe ((isUnionChain_cellChain R).mono
        (Order.le_succ (q : WithTop (CellClass R)))))
      (Subfunctor.lift _ (range_le_cellChain_succ q)) := by
  apply IsPushout.of_forall_isPushout_app
  intro b
  have : Mono ((Subfunctor.homOfLe
      ((isUnionChain_cellChain R).mono (Order.le_succ (q : WithTop (CellClass R))))).app b) :=
    (mono_iff_injective _).2 fun _ _ h ↦ by
      have h' := congrArg Subtype.val h
      exact Subtype.ext h'
  apply Types.isPushout_of_isPullback_of_mono'
  · rw [Types.isPullback_iff]
    refine ⟨?_, ?_, ?_⟩
    · ext f
      rfl
    · rintro f f' ⟨-, h⟩
      exact Subtype.ext h
    · intro y f h
      have h' : y.1 = Y.map f.down.op (rep q).cell := congrArg Subtype.val h
      have hf : ¬IsSplitEpi f.down := fun hf ↦
        map_not_mem_cellChain_of_isSplitEpi q (b := b.unop) f.down hf (h' ▸ y.2)
      exact ⟨⟨f, hf⟩, Subtype.ext h'.symm, rfl⟩
  · refine Set.eq_univ_of_forall fun ⟨y, hy⟩ ↦ ?_
    simp only [Set.sup_eq_union]
    rw [(isUnionChain_cellChain R).succ, Subfunctor.max_obj] at hy
    rcases hy with hy | hy
    · exact Or.inl ⟨⟨y, hy⟩, rfl⟩
    · obtain ⟨g, hg⟩ := (mem_cellImage_iff q _).1 hy
      exact Or.inr ⟨⟨g⟩, Subtype.ext hg⟩
  · intro f f' hf hf' h
    have hs : ∀ g : (uliftYoneda.{w}.obj (rep q).obj).obj b,
        g ∉ Set.range ((uliftBoundary.{w} (rep q).obj).ι.app b) → IsSplitEpi g.down := by
      intro g hg
      by_contra hn
      exact hg ⟨⟨g, hn⟩, rfl⟩
    exact ULift.ext _ _ (eq_of_map_eq_of_isSplitEpi_of_dominant q hq (b := b.unop) f.down f'.down
      (hs f hf) (hs f' hf') (congrArg Subtype.val h))

theorem isPushout_boundaryInclusion [HasTrivialAutomorphisms A] (q : CellClass R) :
    IsPushout (Subfunctor.lift _ (range_boundary_ι_comp_le_cellChain q))
      (uliftBoundary.{w} (rep q).obj).ι
      (Subfunctor.homOfLe ((isUnionChain_cellChain R).mono
        (Order.le_succ (q : WithTop (CellClass R)))))
      (Subfunctor.lift _ (range_le_cellChain_succ q)) :=
  isPushout_boundaryInclusion_of_dominant q fun _ _ ↦ Subsingleton.elim _ _

theorem isPushout_attach [HasTrivialAutomorphisms A] (T : Subfunctor Y) {a : A}
    {x : Y.obj (op a)} (hx : IsNondegenerate Y x) (hxT : x ∉ T.obj (op a))
    (hbd : Subfunctor.range ((uliftBoundary.{w} a).ι ≫ uliftYonedaEquiv.symm x) ≤ T) :
    IsPushout (Subfunctor.lift _ hbd) (uliftBoundary.{w} a).ι
      (Subfunctor.homOfLe (le_sup_left : T ≤ T ⊔ Subfunctor.range (uliftYonedaEquiv.symm x)))
      (Subfunctor.lift _ le_sup_right) := by
  apply IsPushout.of_forall_isPushout_app
  intro b
  have : Mono ((Subfunctor.homOfLe
      (le_sup_left : T ≤ T ⊔ Subfunctor.range (uliftYonedaEquiv.symm x))).app b) :=
    (mono_iff_injective _).2 fun _ _ h ↦ by
      have h' := congrArg Subtype.val h
      exact Subtype.ext h'
  apply Types.isPushout_of_isPullback_of_mono'
  · rw [Types.isPullback_iff]
    refine ⟨?_, ?_, ?_⟩
    · ext f
      rfl
    · rintro f f' ⟨-, h⟩
      exact Subtype.ext h
    · intro y f h
      have h' : y.1 = Y.map f.down.op x := congrArg Subtype.val h
      have hf : ¬IsSplitEpi f.down := fun hf ↦ hxT (by
        have : Y.map (section_ f.down).op (Y.map f.down.op x) ∈ T.obj (op a) :=
          T.map _ (h' ▸ y.2)
        rwa [← Functor.map_comp_apply, ← op_comp, IsSplitEpi.id, op_id,
          Functor.map_id_apply] at this)
      exact ⟨⟨f, hf⟩, Subtype.ext h'.symm, rfl⟩
  · refine Set.eq_univ_of_forall fun ⟨y, hy⟩ ↦ ?_
    simp only [Set.sup_eq_union]
    rw [Subfunctor.max_obj] at hy
    rcases hy with hy | ⟨g, rfl⟩
    · exact Or.inl ⟨⟨y, hy⟩, rfl⟩
    · exact Or.inr ⟨g, rfl⟩
  · intro f f' hf hf' h
    have hs : ∀ g : (uliftYoneda.{w}.obj a).obj b,
        g ∉ Set.range ((uliftBoundary.{w} a).ι.app b) → IsSplitEpi g.down := by
      intro g hg
      by_contra hn
      exact hg ⟨⟨g, hn⟩, rfl⟩
    obtain ⟨e, ⟨he, -⟩, -⟩ := existsUnique_iso_of_isNondegenerate Y f.down f'.down _ _
      (hs f hf) hx (hs f' hf') hx (congrArg Subtype.val h)
    rw [Subsingleton.elim e (Iso.refl a), Iso.refl_hom, Category.comp_id] at he
    exact ULift.ext _ _ he

end Cells

section Main

variable {A : Type v} [SmallCategory A] [EZCategory A]

theorem saturation_boundaryInclusions_ι [HasTrivialAutomorphisms A]
    {Y : Aᵒᵖ ⥤ Type (max w v)} (R : Subfunctor Y) :
    saturation.{max w v} (boundaryInclusions.{w} A) R.ι :=
  (isUnionChain_cellChain R).ι_mem (cellChain_top R) _ fun q ↦
    MorphismProperty.of_isPushout (isPushout_boundaryInclusion q)
      (le_saturation.{max w v} _ _ (MorphismProperty.ofHoms.mk (rep q).obj))

theorem monomorphisms_eq_saturation_boundaryInclusions [HasTrivialAutomorphisms A] :
    MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)) =
      saturation.{max w v} (boundaryInclusions.{w} A) := by
  refine le_antisymm (fun K X i (hi : Mono i) ↦ ?_)
    (saturation_le _ _ (boundaryInclusions_le_monomorphisms.{w} A))
  rw [← Subfunctor.toRange_ι i]
  exact MorphismProperty.comp_mem _ _ _
    (isomorphisms_le_of_containsIdentities _ _ (MorphismProperty.isomorphisms.infer_property _))
    (saturation_boundaryInclusions_ι _)

end Main

end EZCategory

end Atoms.Homotopical
