import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.CartesianFibration
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.CartesianPrism

open CategoryTheory Limits Simplicial MonoidalCategory

universe u

namespace SSet

section Lifting

private lemma forall_hasLift_iff {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D}
    (hF : F.FullyFaithful) {A B X Y : C} {i : A ⟶ B} {p : X ⟶ Y} {A' B' : D} {i' : A' ⟶ B'}
    (e : Arrow.mk i' ≅ Arrow.mk (F.map i)) (P : (A ⟶ X) → Prop) (P' : (A' ⟶ F.obj X) → Prop)
    (hP : ∀ a, P a ↔ P' (e.hom.left ≫ F.map a)) :
    (∀ (a : A ⟶ X) (b : B ⟶ Y) (sq : CommSq a i p b), P a → sq.HasLift) ↔
      ∀ (a' : A' ⟶ F.obj X) (b' : B' ⟶ F.obj Y) (sq' : CommSq a' i' (F.map p) b'),
        P' a' → sq'.HasLift := by
  have he₁ : i' ≫ e.hom.right = e.hom.left ≫ F.map i := (Arrow.w e.hom).symm
  have he₂ : F.map i ≫ e.inv.right = e.inv.left ≫ i' := (Arrow.w e.inv).symm
  refine ⟨fun h a' b' sq' ha' ↦ ?_, fun h a b sq ha ↦ ?_⟩
  · have ha : a' = e.hom.left ≫ F.map (hF.preimage (e.inv.left ≫ a')) := by
      rw [hF.map_preimage, Arrow.hom_inv_id_left_assoc]
    have hb : b' = e.hom.right ≫ F.map (hF.preimage (e.inv.right ≫ b')) := by
      rw [hF.map_preimage, Arrow.hom_inv_id_right_assoc]
    have sq : CommSq (hF.preimage (e.inv.left ≫ a')) i p (hF.preimage (e.inv.right ≫ b')) :=
      ⟨hF.map_injective (by rw [F.map_comp, F.map_comp, hF.map_preimage, hF.map_preimage,
        Category.assoc, sq'.w, ← Category.assoc, ← he₂, Category.assoc])⟩
    obtain ⟨l⟩ := (h _ _ sq ((hP _).2 (ha ▸ ha'))).exists_lift
    refine ⟨⟨⟨e.hom.right ≫ F.map l.l, ?_, ?_⟩⟩⟩
    · rw [← Category.assoc, he₁, Category.assoc, ← F.map_comp, l.fac_left, ← ha]
    · rw [Category.assoc, ← F.map_comp, l.fac_right, ← hb]
  · have sq' : CommSq (e.hom.left ≫ F.map a) i' (F.map p) (e.hom.right ≫ F.map b) := ⟨by
      rw [Category.assoc, ← F.map_comp, sq.w, F.map_comp, ← Category.assoc, ← he₁,
        Category.assoc]⟩
    obtain ⟨l⟩ := (h _ _ sq' ((hP a).1 ha)).exists_lift
    refine ⟨⟨⟨hF.preimage (e.inv.right ≫ l.l), hF.map_injective ?_, hF.map_injective ?_⟩⟩⟩
    · rw [F.map_comp, hF.map_preimage, ← Category.assoc, he₂, Category.assoc, l.fac_left,
        Arrow.inv_hom_id_left_assoc]
    · rw [F.map_comp, hF.map_preimage, Category.assoc, l.fac_right, Arrow.inv_hom_id_right_assoc]

end Lifting

section Dictionary

variable {X Y S : SSet.{u}}

def edgeOp (f : Δ[1] ⟶ X) : Δ[1] ⟶ X.op :=
  (stdSimplex.opIso ⦋1⦌).inv ≫ opFunctor.map f

theorem yonedaEquiv_edgeOp (f : Δ[1] ⟶ X) :
    yonedaEquiv (edgeOp f) = opObjEquiv.symm (yonedaEquiv f) :=
  stdSimplex.yonedaEquiv_opIso_inv_comp f

theorem edgeOp_yonedaEquiv_symm (e : X _⦋1⦌) :
    edgeOp (yonedaEquiv.symm e) = yonedaEquiv.symm (opObjEquiv.symm e) :=
  yonedaEquiv.injective (by rw [yonedaEquiv_edgeOp, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply])

@[reassoc]
theorem edgeOp_comp (f : Δ[1] ⟶ X) (g : X ⟶ Y) :
    edgeOp (f ≫ g) = edgeOp f ≫ opFunctor.map g := by
  rw [edgeOp, edgeOp, Functor.map_comp, Category.assoc]

theorem edgeOp_injective : Function.Injective (edgeOp (X := X)) := fun _ _ h ↦
  opFunctor.map_injective ((cancel_epi (stdSimplex.opIso ⦋1⦌).inv).1 h)

theorem edgeOp_surjective : Function.Surjective (edgeOp (X := X)) := fun f ↦
  ⟨yonedaEquiv.symm (opObjEquiv (yonedaEquiv f)), by
    rw [edgeOp_yonedaEquiv_symm, Equiv.symm_apply_apply, Equiv.symm_apply_apply]⟩

private lemma δ_comp_opIso_inv_comp {n : ℕ} (σ : Δ[n + 1] ⟶ X) (i : Fin (n + 2)) :
    stdSimplex.δ i ≫ (stdSimplex.opIso ⦋n + 1⦌).inv ≫ opFunctor.map σ =
      (stdSimplex.opIso ⦋n⦌).inv ≫ opFunctor.map (stdSimplex.δ i.rev ≫ σ) :=
  yonedaEquiv.injective (by rw [stdSimplex.yonedaEquiv_δ_comp,
    stdSimplex.yonedaEquiv_opIso_inv_comp, stdSimplex.yonedaEquiv_opIso_inv_comp, op_δ,
    Equiv.apply_symm_apply, stdSimplex.yonedaEquiv_δ_comp])

theorem δ_comp_edgeOp_eq_iff (f : Δ[1] ⟶ X) (i : Fin 2) (x : X _⦋0⦌) :
    stdSimplex.δ i ≫ edgeOp f = yonedaEquiv.symm (opObjEquiv.symm x) ↔
      stdSimplex.δ i.rev ≫ f = yonedaEquiv.symm x := by
  rw [← yonedaEquiv.apply_eq_iff_eq, ← yonedaEquiv.apply_eq_iff_eq, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply, stdSimplex.yonedaEquiv_δ_comp, stdSimplex.yonedaEquiv_δ_comp,
    yonedaEquiv_edgeOp, op_δ, Equiv.apply_symm_apply, Equiv.apply_eq_iff_eq]

theorem nonempty_invStruct_edgeOp_iff (f : Δ[1] ⟶ X) :
    Nonempty (Edge.mk' (yonedaEquiv (edgeOp f))).InvStruct ↔
      Nonempty (Edge.mk' (yonedaEquiv f)).InvStruct := by
  rw [yonedaEquiv_edgeOp]
  refine ⟨fun h ↦ ?_, nonempty_invStruct_op _⟩
  obtain ⟨I⟩ := nonempty_invStruct_op _ h
  exact ⟨(I.map (opFunctorCompOpFunctorIso.app X).hom).ofEq rfl⟩

private lemma exists_iso_pullback_op (p : X ⟶ S) {K K' : SSet.{u}} (b : K ⟶ S) (e : K.op ≅ K')
    (b' : K' ⟶ S.op) (hb : e.inv ≫ opFunctor.map b = b') :
    ∃ Q : (pullback p b).op ≅ pullback (opFunctor.map p) b',
      Q.hom ≫ pullback.fst _ _ = opFunctor.map (pullback.fst p b) ∧
        Q.hom ≫ pullback.snd _ _ = opFunctor.map (pullback.snd p b) ≫ e.hom :=
  have h := isPullback_op_pullback p b e b' hb
  ⟨h.isoPullback, h.isoPullback_hom_fst, h.isoPullback_hom_snd⟩

private lemma isCartesianEdge_comp_iff_of_iso {X' S' : SSet.{u}} {p : X ⟶ S} {p' : X' ⟶ S'}
    (q : X' ≅ X) (g : S' ≅ S) (w : q.hom ≫ p = p' ≫ g.hom) (f : Δ[1] ⟶ X') :
    IsCartesianEdge p (f ≫ q.hom) ↔ IsCartesianEdge p' f :=
  ⟨fun h ↦ IsCartesianEdge.of_isPullback (IsPullback.of_horiz_isIso ⟨w⟩) h, fun h ↦
    IsCartesianEdge.of_isPullback (IsPullback.of_horiz_isIso (fst := q.inv) (g := g.inv)
      ⟨(Iso.eq_comp_inv g).2 (by rw [Category.assoc, ← w, Iso.inv_hom_id_assoc])⟩)
      (by rwa [Category.assoc, q.hom_inv_id, Category.comp_id])⟩

end Dictionary

variable {X S : SSet.{u}}

def IsCocartesianEdge (p : X ⟶ S) (f : Δ[1] ⟶ X) : Prop :=
  IsCartesianEdge (opFunctor.map p) (edgeOp f)

def IsLocallyCocartesianEdge (p : X ⟶ S) (f : Δ[1] ⟶ X) : Prop :=
  IsLocallyCartesianEdge (opFunctor.map p) (edgeOp f)

theorem isCocartesianEdge_iff_hasLift_horn (p : X ⟶ S) (f : Δ[1] ⟶ X) :
    IsCocartesianEdge p f ↔
      ∀ (n : ℕ) (a : (Λ[n + 2, 0] : SSet.{u}) ⟶ X) (b : Δ[n + 2] ⟶ S)
        (sq : CommSq a Λ[n + 2, 0].ι p b),
        a.app _ (horn.edge (n + 2) 0 0 1 (Fin.zero_le _) (by simp)) = yonedaEquiv f →
          sq.HasLift := by
  rw [IsCocartesianEdge, isCartesianEdge_iff_hasLift_horn]
  refine forall_congr' fun n ↦ (forall_hasLift_iff opEquivalence.fullyFaithfulFunctor
    (hornArrowIsoOp (n + 2) 0 (Fin.last _) (Fin.rev_zero _)) _ _ fun a ↦ ?_).symm
  have hx : opObjEquiv ((hornArrowIsoOp (n + 2) 0 (Fin.last _) (Fin.rev_zero _)).hom.left.app _
      (horn.edge (n + 2) (Fin.last (n + 2)) (Fin.last (n + 1)).castSucc (Fin.last (n + 2))
        (Fin.le_last _) (by simp))) = horn.edge (n + 2) 0 0 1 (Fin.zero_le _) (by simp) :=
    Subtype.ext (stdSimplex.ext _ _ fun i ↦ by
      fin_cases i
      · exact Fin.rev_last _
      · exact (Fin.rev_castSucc _).trans (congrArg Fin.succ (Fin.rev_last _)))
  rw [yonedaEquiv_edgeOp, ← hx]
  exact (Equiv.apply_eq_iff_eq opObjEquiv.symm).symm

theorem isCocartesianEdge_of_isIso (p : X ⟶ S) [IsIso p] (f : Δ[1] ⟶ X) :
    IsCocartesianEdge p f :=
  isCartesianEdge_of_isIso _ _

theorem IsCocartesianEdge.of_isPullback {X' S' : SSet.{u}} {p : X ⟶ S} {p' : X' ⟶ S'}
    {q : X' ⟶ X} {g : S' ⟶ S} (h : IsPullback q p' p g) {f : Δ[1] ⟶ X'}
    (hf : IsCocartesianEdge p (f ≫ q)) : IsCocartesianEdge p' f :=
  IsCartesianEdge.of_isPullback (h.map opFunctor) (by rw [← edgeOp_comp]; exact hf)

theorem IsCocartesianEdge.comp_iff {Y Z : SSet.{u}} (p : X ⟶ Y) (q : Y ⟶ Z)
    [InnerFibration p] {f : Δ[1] ⟶ X} (hq : IsCocartesianEdge q (f ≫ p)) :
    IsCocartesianEdge p f ↔ IsCocartesianEdge (p ≫ q) f := by
  rw [IsCocartesianEdge, IsCocartesianEdge, Functor.map_comp]
  exact IsCartesianEdge.comp_iff _ _ (by rw [← edgeOp_comp]; exact hq)

theorem invStruct_iff_isCocartesianEdge {C D : SSet.{u}} [C.Quasicategory] [D.Quasicategory]
    (p : C ⟶ D) [InnerFibration p] (f : Δ[1] ⟶ C) :
    Nonempty (Edge.mk' (yonedaEquiv f)).InvStruct ↔
      IsCocartesianEdge p f ∧ Nonempty (Edge.mk' (yonedaEquiv (f ≫ p))).InvStruct := by
  rw [← nonempty_invStruct_edgeOp_iff, ← nonempty_invStruct_edgeOp_iff (f ≫ p), edgeOp_comp]
  exact invStruct_iff_isCartesianEdge (opFunctor.map p) (edgeOp f)

theorem isCocartesianEdge_id {C D : SSet.{u}} [C.Quasicategory] [D.Quasicategory]
    (p : C ⟶ D) [InnerFibration p] (x : C _⦋0⦌) :
    IsCocartesianEdge p (yonedaEquiv.symm (Edge.id x).edge) :=
  ((invStruct_iff_isCocartesianEdge p _).1
    ⟨(Edge.InvStruct.invStructId x).ofEq (by rw [Edge.mk'_edge, Equiv.apply_symm_apply])⟩).1

theorem isCocartesianEdge_δ_zero_iff_δ_one {C D : SSet.{u}} [D.Quasicategory]
    (p : C ⟶ D) [InnerFibration p] (σ : Δ[2] ⟶ C)
    (hf : IsCocartesianEdge p (stdSimplex.δ 2 ≫ σ)) :
    IsCocartesianEdge p (stdSimplex.δ 0 ≫ σ) ↔ IsCocartesianEdge p (stdSimplex.δ 1 ≫ σ) := by
  have h := isCartesianEdge_δ_two_iff_δ_one (opFunctor.map p)
    ((stdSimplex.opIso ⦋2⦌).inv ≫ opFunctor.map σ) (by rw [δ_comp_opIso_inv_comp]; exact hf)
  rwa [δ_comp_opIso_inv_comp, δ_comp_opIso_inv_comp] at h

theorem isCocartesianEdge_iff_forall_pullback (p : X ⟶ S) (f : Δ[1] ⟶ X) :
    IsCocartesianEdge p f ↔ ∀ (n : ℕ) (b : Δ[n] ⟶ S) (f' : Δ[1] ⟶ pullback p b),
      f' ≫ pullback.fst p b = f → IsCocartesianEdge (pullback.snd p b) f' := by
  rw [IsCocartesianEdge, isCartesianEdge_iff_forall_pullback]
  refine forall_congr' fun n ↦ ⟨fun h b f' hf' ↦ ?_, fun h b' f'' hf'' ↦ ?_⟩
  · obtain ⟨Q, hQ₁, hQ₂⟩ := exists_iso_pullback_op p b (stdSimplex.opIso ⦋n⦌) _ rfl
    exact (isCartesianEdge_comp_iff_of_iso Q (stdSimplex.opIso ⦋n⦌) hQ₂ _).1
      (h _ (edgeOp f' ≫ Q.hom) (by rw [Category.assoc, hQ₁, ← edgeOp_comp, hf']))
  · obtain ⟨b, hb⟩ : ∃ b : Δ[n] ⟶ S, (stdSimplex.opIso ⦋n⦌).inv ≫ opFunctor.map b = b' :=
      ⟨_, by rw [Functor.map_preimage, Iso.inv_hom_id_assoc]⟩
    obtain ⟨Q, hQ₁, hQ₂⟩ := exists_iso_pullback_op p b (stdSimplex.opIso ⦋n⦌) b' hb
    obtain ⟨f', hf'⟩ := edgeOp_surjective (f'' ≫ Q.inv)
    have e : f'' = edgeOp f' ≫ Q.hom := by rw [hf', Category.assoc, Q.inv_hom_id, Category.comp_id]
    rw [e]
    refine (isCartesianEdge_comp_iff_of_iso Q (stdSimplex.opIso ⦋n⦌) hQ₂ _).2
      (h b f' (edgeOp_injective ?_))
    rw [edgeOp_comp, ← hQ₁, ← Category.assoc, ← e, hf'']

theorem isLocallyCocartesianEdge_iff (p : X ⟶ S) (f : Δ[1] ⟶ X) :
    IsLocallyCocartesianEdge p f ↔ IsCocartesianEdge (pullback.snd p (f ≫ p))
      (pullback.lift f (𝟙 Δ[1]) (Category.id_comp _).symm) := by
  obtain ⟨Q, hQ₁, hQ₂⟩ := exists_iso_pullback_op p (f ≫ p) (stdSimplex.opIso ⦋1⦌) _
    (edgeOp_comp f p)
  rw [IsLocallyCocartesianEdge, IsCocartesianEdge, IsLocallyCartesianEdge,
    ← isCartesianEdge_comp_iff_of_iso Q (stdSimplex.opIso ⦋1⦌) hQ₂]
  refine Iff.of_eq (congrArg _ (pullback.hom_ext ?_ ?_))
  · rw [pullback.lift_fst, Category.assoc, hQ₁, ← edgeOp_comp, pullback.lift_fst]
  · rw [pullback.lift_snd, Category.assoc, hQ₂, ← edgeOp_comp_assoc, pullback.lift_snd, edgeOp,
      CategoryTheory.Functor.map_id, Category.comp_id, Iso.inv_hom_id]

theorem IsCocartesianEdge.of_isLocallyCocartesianEdge (p : X ⟶ S) [InnerFibration p]
    {e e₀ : Δ[1] ⟶ X} (he₀ : IsCocartesianEdge p e₀) (hp : e₀ ≫ p = e ≫ p)
    (hs : stdSimplex.δ 1 ≫ e₀ = stdSimplex.δ 1 ≫ e) (he : IsLocallyCocartesianEdge p e) :
    IsCocartesianEdge p e := by
  refine IsCartesianEdge.of_isLocallyCartesianEdge (opFunctor.map p) he₀
    (by rw [← edgeOp_comp, ← edgeOp_comp, hp]) ?_ he
  have h₀ : (0 : Fin 2).rev = 1 := rfl
  rw [edgeOp, edgeOp, δ_comp_opIso_inv_comp, δ_comp_opIso_inv_comp, h₀, hs]

section Prism

variable (n : ℕ)

noncomputable def prismFirstEdge :
    Δ[1] ⟶ ((Λ[1, 0] : (Δ[1] : SSet.{u}).Subcomplex).unionProd (∂Δ[n + 1]) : SSet.{u}) :=
  Subcomplex.lift (CartesianMonoidalCategory.lift (𝟙 _)
    (stdSimplex.map (SimplexCategory.const ⦋1⦌ ⦋n + 1⦌ 0))) (by
      rw [Subcomplex.range_eq_ofSimplex, Subcomplex.ofSimplex_le_iff]
      refine (Subcomplex.mem_unionProd_iff _ _ _).2 (Or.inl ?_)
      rw [mem_boundary_iff_notMem_range]
      exact ⟨Fin.last _, fun ⟨t, ht⟩ ↦ (Fin.last_pos : 0 < Fin.last (n + 1)).ne ht⟩)

private noncomputable def prismOpIso :
    (Δ[1] ⊗ Δ[n + 1] : SSet.{u}) ≅ (Δ[1] ⊗ Δ[n + 1] : SSet.{u}).op :=
  ((stdSimplex.opIso ⦋1⦌).symm ⊗ᵢ (stdSimplex.opIso ⦋n + 1⦌).symm) ≪≫
    Functor.Monoidal.μIso opFunctor _ _

private lemma preimage_prismOpIso :
    ((Λ[1, 0] : (Δ[1] : SSet.{u}).Subcomplex).unionProd (∂Δ[n + 1])).op.preimage
      (prismOpIso n).hom = (Λ[1, 1] : (Δ[1] : SSet.{u}).Subcomplex).unionProd (∂Δ[n + 1]) := by
  refine Subfunctor.ext (funext fun d ↦ Set.ext fun x ↦ ?_)
  have h₁ := congrArg (fun A : (Δ[1] : SSet.{u}).Subcomplex ↦ x.1 ∈ A.obj d)
    (op_horn.{u} (n := 1) 0)
  have h₂ := congrArg (fun A : (Δ[n + 1] : SSet.{u}).Subcomplex ↦ x.2 ∈ A.obj d)
    (op_boundary.{u} (n + 1))
  simp only [Subcomplex.preimage_obj, Set.mem_preimage] at h₁ h₂ ⊢
  exact (Subcomplex.mem_unionProd_iff _ _ _).trans (((Iff.of_eq h₂).or (Iff.of_eq h₁)).trans
    (Subcomplex.mem_unionProd_iff _ _ _).symm)

private noncomputable def prismArrowIsoOp :
    Arrow.mk ((Λ[1, 1] : (Δ[1] : SSet.{u}).Subcomplex).unionProd (∂Δ[n + 1])).ι ≅
      Arrow.mk (opFunctor.map ((Λ[1, 0] : (Δ[1] : SSet.{u}).Subcomplex).unionProd (∂Δ[n + 1])).ι) :=
  arrowIsoOfPreimage (prismOpIso n) _ _ (preimage_prismOpIso n)

private lemma prismLastEdge_comp_prismArrowIsoOp :
    prismLastEdge n ≫ (prismArrowIsoOp.{u} n).hom.left =
      (stdSimplex.opIso ⦋1⦌).inv ≫ opFunctor.map (prismFirstEdge n) := by
  have hl : (prismLastEdge n ≫ (prismArrowIsoOp.{u} n).hom.left) ≫
      ((Λ[1, 0] : (Δ[1] : SSet.{u}).Subcomplex).unionProd (∂Δ[n + 1])).op.ι =
        (prismLastEdge n ≫ Subcomplex.ι _) ≫ (prismOpIso n).hom :=
    (Category.assoc _ _ _).trans ((congrArg _ (Subcomplex.lift_ι
      (Subcomplex.ι _ ≫ (prismOpIso n).hom) (by rw [← Subcomplex.image_eq_range,
        Subcomplex.image_le_iff, preimage_prismOpIso]))).trans (Category.assoc _ _ _).symm)
  have hr : ((stdSimplex.opIso ⦋1⦌).inv ≫ opFunctor.map (prismFirstEdge n)) ≫
      ((Λ[1, 0] : (Δ[1] : SSet.{u}).Subcomplex).unionProd (∂Δ[n + 1])).op.ι =
        (stdSimplex.opIso ⦋1⦌).inv ≫ opFunctor.map (prismFirstEdge n ≫ Subcomplex.ι _) :=
    (Category.assoc _ _ _).trans
      (congrArg _ (opFunctor.map_comp (prismFirstEdge n) (Subcomplex.ι _)).symm)
  refine (cancel_mono ((Λ[1, 0] : (Δ[1] : SSet.{u}).Subcomplex).unionProd (∂Δ[n + 1])).op.ι).1
    (hl.trans (Eq.trans (yonedaEquiv.injective ?_) hr.symm))
  refine (yonedaEquiv_comp _ _).trans (Eq.trans ?_ (stdSimplex.yonedaEquiv_opIso_inv_comp _).symm)
  apply opObjEquiv.injective
  refine Prod.ext (stdSimplex.ext _ _ fun i ↦ ?_) (stdSimplex.ext _ _ fun i ↦ ?_) <;> fin_cases i
  all_goals first | rfl | exact Fin.rev_last _

end Prism

theorem isCocartesianEdge_iff_hasLift_unionProd (p : X ⟶ S) [InnerFibration p]
    (f : Δ[1] ⟶ X) :
    IsCocartesianEdge p f ↔
      ∀ (n : ℕ)
        (a : ((Λ[1, 0] : (Δ[1] : SSet.{u}).Subcomplex).unionProd (∂Δ[n + 1]) : SSet.{u}) ⟶ X)
        (b : Δ[1] ⊗ Δ[n + 1] ⟶ S) (sq : CommSq a (Λ[1, 0].unionProd ∂Δ[n + 1]).ι p b),
        prismFirstEdge n ≫ a = f → sq.HasLift := by
  rw [IsCocartesianEdge, isCartesianEdge_iff_hasLift_unionProd]
  refine forall_congr' fun n ↦ (forall_hasLift_iff opEquivalence.fullyFaithfulFunctor
    (prismArrowIsoOp n) _ _ fun a ↦ ?_).symm
  refine Iff.trans ⟨fun h ↦ congrArg edgeOp h, fun h ↦ edgeOp_injective h⟩ (Eq.congr_left ?_)
  exact (edgeOp_comp _ _).trans ((congrArg (· ≫ opFunctor.map a)
    (prismLastEdge_comp_prismArrowIsoOp n).symm).trans (Category.assoc _ _ _))

end SSet
