import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.ZeroObject
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
import Atoms.Homotopical.Simplicial.FinalObject

open CategoryTheory Limits Simplicial MorphismProperty HomotopicalAlgebra

universe u

namespace SSet

variable {X : SSet.{u}}

private lemma leftAnodyneExtensions_coherentIso_vertex (b : Bool) :
    leftAnodyneExtensions (yonedaEquiv.symm (cond b coherentIso.x₁ coherentIso.x₀) :
      Δ[0] ⟶ coherentIso.{u}) := fun _ _ q hq ↦
  hasLiftingProperty_coherentIso_vertex_of_horn_zero b q fun _ ↦
    hq _ (.intro 0 (Fin.pos_iff_ne_zero.2 (Fin.last_pos.ne')))

private lemma trivialFibration_of_comp {E Y Z : SSet.{u}} {q : E ⟶ Y} {p : Y ⟶ Z}
    (hq : modelCategoryQuillen.I.rlp q) (hqp : modelCategoryQuillen.I.rlp (q ≫ p)) :
    modelCategoryQuillen.I.rlp p := by
  rw [← rlp_monomorphisms] at hq hqp ⊢
  intro A B i hi
  refine ⟨fun {a b} sq ↦ ?_⟩
  have : Mono i := hi
  obtain ⟨l₀⟩ := ((hq _ (monomorphisms.infer_property (initial.to A))).sq_hasLift
    (CommSq.mk (initial.hom_ext (initial.to E ≫ q) (initial.to A ≫ a)) :
      CommSq (initial.to E) (initial.to A) q a)).exists_lift
  have w : l₀.l ≫ q ≫ p = i ≫ b := by rw [← Category.assoc, l₀.fac_right, sq.w]
  obtain ⟨l⟩ := ((hqp _ hi).sq_hasLift (CommSq.mk w)).exists_lift
  exact ⟨⟨⟨l.l ≫ q, by rw [← Category.assoc, l.fac_left, l₀.fac_right], by
    rw [Category.assoc, l.fac_right]⟩⟩⟩

private lemma trivialFibration_sliceπ_of_leftAnodyne {A X : SSet.{u}} [X.Quasicategory]
    (g : A ⟶ X) {a b : Δ[0] ⟶ A} (ha : leftAnodyneExtensions a) (hb : leftAnodyneExtensions b)
    {c c' : Δ[0] ⟶ X} (hc : a ≫ g = c) (hc' : b ≫ g = c')
    (h : modelCategoryQuillen.I.rlp (sliceπ (Under.mk c))) :
    modelCategoryQuillen.I.rlp (sliceπ (Under.mk c')) := by
  subst hc hc'
  have hg : modelCategoryQuillen.I.rlp (sliceπ (Under.mk g)) := by
    rw [← sliceRes_sliceπ a (Under.mk g)]
    exact modelCategoryQuillen.I.rlp.comp_mem _ _ (trivialFibration_sliceRes ha g) h
  rw [← sliceRes_sliceπ b (Under.mk g)] at hg
  exact trivialFibration_of_comp (trivialFibration_sliceRes hb g) hg

private lemma sliceAtπ_eq_sliceπ (X : SSet.{u}) (ω : X _⦋0⦌) :
    sliceAtπ X ω = sliceπ (Under.mk (yonedaEquiv.symm ω)) :=
  rfl

private lemma isFinal_iff_of_isIso_homMk [X.Quasicategory] {ω ω' : X _⦋0⦌} (e : Edge ω ω')
    (he : IsIso (SSet.Truncated.HomotopyCategory.homMk (V := (SSet.truncation 2).obj X) e)) :
    IsFinal ω ↔ IsFinal ω' := by
  obtain ⟨I⟩ := (isIso_homMk_iff e).1 he
  obtain ⟨g, hg⟩ := exists_coherentIso_extension e I
  have h₀ : yonedaEquiv.symm coherentIso.x₀ ≫ g = yonedaEquiv.symm ω := by
    rw [yonedaEquiv_symm_comp, ← (coherentIso.hom.map g).src_eq, hg, e.src_eq]
  have h₁ : yonedaEquiv.symm coherentIso.x₁ ≫ g = yonedaEquiv.symm ω' := by
    rw [yonedaEquiv_symm_comp, ← (coherentIso.hom.map g).tgt_eq, hg, e.tgt_eq]
  have ha₀ := leftAnodyneExtensions_coherentIso_vertex.{u} false
  have ha₁ := leftAnodyneExtensions_coherentIso_vertex.{u} true
  rw [cond_false] at ha₀
  rw [cond_true] at ha₁
  rw [isFinal_iff_trivialFibration_sliceAtπ, isFinal_iff_trivialFibration_sliceAtπ,
    sliceAtπ_eq_sliceπ, sliceAtπ_eq_sliceπ]
  exact ⟨trivialFibration_sliceπ_of_leftAnodyne g ha₀ ha₁ h₀ h₁,
    trivialFibration_sliceπ_of_leftAnodyne g ha₁ ha₀ h₁ h₀⟩

theorem isFinal_of_isIso_homMk [X.Quasicategory] {ω ω' : X _⦋0⦌} (e : Edge ω ω')
    (he : IsIso (SSet.Truncated.HomotopyCategory.homMk (V := (SSet.truncation 2).obj X) e))
    (h : IsFinal ω) : IsFinal ω' :=
  (isFinal_iff_of_isIso_homMk e he).1 h

private lemma exists_isIso_homMk_op {ω ω' : X _⦋0⦌} (e : Edge ω ω')
    (he : IsIso (SSet.Truncated.HomotopyCategory.homMk (V := (SSet.truncation 2).obj X) e)) :
    ∃ e' : Edge (X := X.op) (opObjEquiv.symm ω') (opObjEquiv.symm ω),
      IsIso (SSet.Truncated.HomotopyCategory.homMk (V := (SSet.truncation 2).obj X.op) e') := by
  let e' : Edge (X := X.op) (opObjEquiv.symm ω') (opObjEquiv.symm ω) :=
    Edge.mk (opObjEquiv.symm e.edge) (by rw [op_δ]; exact congrArg opObjEquiv.symm e.tgt_eq)
      (by rw [op_δ]; exact congrArg opObjEquiv.symm e.src_eq)
  refine ⟨e', ?_⟩
  have : IsIso ((SSet.Truncated.HomotopyCategory.opEquivalence X).functor.map
      (SSet.Truncated.HomotopyCategory.homMk (V := (SSet.truncation 2).obj X.op) e')) := by
    rw [SSet.Truncated.HomotopyCategory.opEquivalence_functor_map_homMk e' e rfl]
    exact @isIso_op _ _ _ _ _ he
  exact isIso_of_reflects_iso _ (SSet.Truncated.HomotopyCategory.opEquivalence X).functor

theorem isInitialObject_of_isIso_homMk [X.Quasicategory] {ω ω' : X _⦋0⦌} (e : Edge ω ω')
    (he : IsIso (SSet.Truncated.HomotopyCategory.homMk (V := (SSet.truncation 2).obj X) e))
    (h : IsInitialObject ω) : IsInitialObject ω' := by
  obtain ⟨e', he'⟩ := exists_isIso_homMk_op e he
  exact (isFinal_iff_of_isIso_homMk e' he').2 h

theorem isZeroObject_of_isIso_homMk [X.Quasicategory] {ω ω' : X _⦋0⦌} (e : Edge ω ω')
    (he : IsIso (SSet.Truncated.HomotopyCategory.homMk (V := (SSet.truncation 2).obj X) e))
    (h : IsZeroObject ω) : IsZeroObject ω' :=
  ⟨isFinal_of_isIso_homMk e he h.1, isInitialObject_of_isIso_homMk e he h.2⟩

noncomputable def isInitialOfIsInitialObject [X.Quasicategory] {ω : X _⦋0⦌}
    (h : IsInitialObject ω) :
    IsInitial (SSet.Truncated.HomotopyCategory.mk (V := (SSet.truncation 2).obj X) ω) :=
  ((isTerminalOfIsFinal h).isTerminalObj
    (SSet.Truncated.HomotopyCategory.opEquivalence X).functor _).unop

theorem isZero_of_isZeroObject [X.Quasicategory] {ω : X _⦋0⦌} (h : IsZeroObject ω) :
    IsZero (SSet.Truncated.HomotopyCategory.mk (V := (SSet.truncation 2).obj X) ω) :=
  have hT := isTerminalOfIsFinal h.1
  have hI := isInitialOfIsInitialObject h.2
  ⟨fun _ ↦ ⟨⟨⟨hI.to _⟩, fun _ ↦ hI.hom_ext _ _⟩⟩, fun _ ↦ ⟨⟨⟨hT.from _⟩, fun _ ↦ hT.hom_ext _ _⟩⟩⟩

theorem hasZeroObject_homotopyCategory [X.Quasicategory] (h : X.IsPointed) :
    HasZeroObject (SSet.Truncated.HomotopyCategory ((SSet.truncation 2).obj X)) :=
  have ⟨_, hω⟩ := h
  ⟨⟨_, isZero_of_isZeroObject hω⟩⟩

theorem comp_eq_comp_of_isZeroObject [X.Quasicategory] {x y z z' : X _⦋0⦌}
    (hz : IsZeroObject z) (hz' : IsZeroObject z')
    (a : SSet.Truncated.HomotopyCategory.mk (V := (SSet.truncation 2).obj X) x ⟶
      SSet.Truncated.HomotopyCategory.mk z)
    (b : SSet.Truncated.HomotopyCategory.mk (V := (SSet.truncation 2).obj X) z ⟶
      SSet.Truncated.HomotopyCategory.mk y)
    (a' : SSet.Truncated.HomotopyCategory.mk (V := (SSet.truncation 2).obj X) x ⟶
      SSet.Truncated.HomotopyCategory.mk z')
    (b' : SSet.Truncated.HomotopyCategory.mk (V := (SSet.truncation 2).obj X) z' ⟶
      SSet.Truncated.HomotopyCategory.mk y) :
    a ≫ b = a' ≫ b' := by
  have H := isZero_of_isZeroObject hz
  have H' := isZero_of_isZeroObject hz'
  rw [← Category.id_comp b, ← (H.iso H').hom_inv_id, Category.assoc, ← Category.assoc a,
    H'.eq_of_tgt (a ≫ (H.iso H').hom) a', H'.eq_of_src ((H.iso H').inv ≫ b) b']

theorem isPointed_iff [X.Quasicategory] :
    X.IsPointed ↔ ∃ i t : X _⦋0⦌, IsInitialObject i ∧ IsFinal t ∧ Nonempty (Edge t i) := by
  refine ⟨fun ⟨ω, hω⟩ ↦ ⟨ω, ω, hω.2, hω.1, ⟨Edge.id ω⟩⟩, fun ⟨i, t, hi, ht, ⟨f⟩⟩ ↦ ?_⟩
  have hI := isInitialOfIsInitialObject hi
  have hT := isTerminalOfIsFinal ht
  have hf : IsIso (SSet.Truncated.HomotopyCategory.homMk (V := (SSet.truncation 2).obj X) f) :=
    ⟨hI.to _, hT.hom_ext _ _, hI.hom_ext _ _⟩
  exact ⟨i, isFinal_of_isIso_homMk f hf ht, hi⟩

private lemma map_const_yonedaEquiv {m : ℕ} (v : Δ[m] ⟶ X) (i : Fin (m + 1)) :
    X.map (SimplexCategory.const ⦋0⦌ ⦋m⦌ i).op (yonedaEquiv v) =
      v.app _ (stdSimplex.obj₀Equiv.symm i) :=
  (NatTrans.naturality_apply v _ _).symm.trans rfl

theorem trivialFibration_zeroSubcomplex [X.Quasicategory] (h : X.IsPointed) :
    modelCategoryQuillen.I.rlp (stdSimplex.isTerminalObj₀.from (zeroSubcomplex X : SSet.{u})) := by
  suffices H : ∀ n, HasLiftingProperty (boundary.{u} n).ι
      (stdSimplex.isTerminalObj₀.from (zeroSubcomplex X : SSet.{u})) from fun _ _ _ ⟨n⟩ ↦ H n
  intro n
  refine ⟨fun {a b} _ ↦ ?_⟩
  cases n with
  | zero =>
    obtain ⟨ω, hω⟩ := h
    exact ⟨⟨⟨yonedaEquiv.symm ⟨ω, (mem_zeroSubcomplex_obj_zero_iff ω).2 hω⟩, boundary.hom_ext₀,
      stdSimplex.isTerminalObj₀.hom_ext _ _⟩⟩⟩
  | succ n =>
    have hc := ((mem_zeroSubcomplex_obj_zero_iff _).1 (a.app _ (boundary.lastVertex n)).2).1
    obtain ⟨v, hv⟩ := (isFinal_iff_extend_boundary _).1 hc n (a ≫ (zeroSubcomplex X).ι) rfl
    have hle : Subcomplex.range v ≤ zeroSubcomplex X := by
      rw [Subcomplex.range_eq_ofSimplex, Subcomplex.ofSimplex_le_iff]
      intro i
      rw [map_const_yonedaEquiv]
      have hi : stdSimplex.obj₀Equiv.symm i ∈
          (∂Δ[n + 1] : (Δ[n + 1] : SSet.{u}).Subcomplex).obj _ := by
        rw [boundary_obj_eq_univ 0 (n + 1)]
        trivial
      have hv' : v.app _ (stdSimplex.obj₀Equiv.symm i) = (a.app _ ⟨_, hi⟩).1 :=
        ConcreteCategory.congr_hom (congr_app hv _) ⟨_, hi⟩
      rw [hv']
      exact (mem_zeroSubcomplex_obj_zero_iff _).1 (a.app _ _).2
    refine ⟨⟨⟨Subcomplex.lift v hle, ?_, stdSimplex.isTerminalObj₀.hom_ext _ _⟩⟩⟩
    rw [← cancel_mono (zeroSubcomplex X).ι, Category.assoc, Subcomplex.lift_ι, hv]

end SSet
