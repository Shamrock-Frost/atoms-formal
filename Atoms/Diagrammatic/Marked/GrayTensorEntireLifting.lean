import Atoms.Diagrammatic.Marked.Acyclic
import Atoms.Diagrammatic.Marked.GrayTensorEntireBoxes
import Atoms.Diagrammatic.Marked.GrayTensorMonoidal

open CategoryTheory Limits Opposite MorphismProperty
open Atoms.Homotopical Atoms.Shape

universe u

namespace Atoms.Diagrammatic

open MarkedPresheaf (forget)

theorem mem_marked_of_rlp_markingGeneratorsAbove (n : ℕ∞) {Y S : MarkedDiagSet.{u}} (y : Y ⟶ S)
    (hy : (markingGeneratorsAbove n).rlp y) {U : Atom} (c : diagram Y.underlying U)
    (hn : n < U.dimension) (hc : (forget.map y).app (op U) c ∈ S.marked U) : c ∈ Y.marked U := by
  have hU : 0 < U.dimension := Nat.cast_pos.1 (lt_of_le_of_lt (zero_le (a := n)) hn)
  let q := ((MarkedPresheaf.flatForgetAdjunction atomMarking).homEquiv _ Y).symm
    (uliftYonedaEquiv.symm c)
  have := hy _ (MorphismProperty.ofHoms.mk (⟨U, hn⟩ : {U : Atom // n < U.dimension}))
  have h₁ : (uliftYonedaEquiv.symm c : uliftYoneda.{u}.obj U ⟶ forget.obj Y) ≫ forget.map y =
      uliftYonedaEquiv.symm ((forget.map y).app (op U) c) := by
    apply uliftYonedaEquiv.injective
    rw [uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
    exact congrArg _ (uliftYonedaEquiv.apply_symm_apply c)
  have sq : CommSq q (MarkedDiagSet.markingInclusion U hU) y
      (MarkedDiagSet.markedAtomHom U hU _ hc) :=
    ⟨MarkedPresheaf.hom_ext (h₁.trans (Category.id_comp _).symm)⟩
  have hfq : forget.map sq.lift = uliftYonedaEquiv.symm c :=
    (Category.id_comp _).symm.trans ((forget.map_comp _ _).symm.trans
      (congrArg forget.map sq.fac_left))
  have hx : (forget.map sq.lift).app (op U) ⟨𝟙 U⟩ = c := by
    rw [hfq]
    exact uliftYonedaEquiv.apply_symm_apply c
  rw [← hx]
  exact MarkedPresheaf.map_mem_marked sq.lift
    ((MarkedPresheaf.mem_marked_ofMarking _ _ U _).2 (Or.inr (IsIso.id U)))

private theorem forget_map_inv_app_hom_app {X Y : MarkedDiagSet.{u}} (i : X ≅ Y) {T : Atom}
    (c : diagram X.underlying T) :
    (forget.map i.inv).app (op T) ((forget.map i.hom).app (op T) c) = c :=
  congrArg (fun f : forget.obj X ⟶ forget.obj X => f.app (op T) c)
    ((forget.map_comp _ _).symm.trans ((congrArg forget.map i.hom_inv_id).trans (forget.map_id _)))

private theorem mem_marked_of_entire_restriction {A B P Q Y S : MarkedDiagSet.{u}}
    (a : A ⟶ B) [IsIso (forget.map a)] (y : Y ⟶ S) [HasLiftingProperty a y]
    (i : P ⟶ Q) {u : P ⟶ Y} {v : Q ⟶ S} (csq : CommSq u i y v)
    (l : forget.obj Q ⟶ forget.obj Y) (hl : forget.map i ≫ l = forget.map u)
    (r : A ⟶ P) (s : B ⟶ Q) (hrs : r ≫ i = a ≫ s)
    {T : Atom} (w : diagram B.underlying T) (hw : w ∈ B.marked T) :
    l.app (op T) ((forget.map s).app (op T) w) ∈ Y.marked T := by
  have csq' : CommSq (r ≫ u) a y (s ≫ v) :=
    ⟨(Category.assoc _ _ _).trans ((congrArg (r ≫ ·) csq.w).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ v) hrs).trans
        (Category.assoc _ _ _))))⟩
  have hh : forget.map s ≫ l = forget.map csq'.lift := by
    refine (cancel_epi (forget.map a)).1 ?_
    have hq : forget.map a ≫ forget.map s = forget.map r ≫ forget.map i :=
      (forget.map_comp a s).symm.trans
        ((congrArg forget.map hrs.symm).trans (forget.map_comp r i))
    rw [← Category.assoc, hq, Category.assoc, hl]
    exact (forget.map_comp r u).symm.trans
      ((congrArg forget.map csq'.fac_left.symm).trans (forget.map_comp a csq'.lift))
  exact (ConcreteCategory.congr_hom (congr_app hh (op T)) w) ▸
    MarkedPresheaf.map_mem_marked csq'.lift hw

private theorem tensorVertex_naturality
    (F : MarkedDiagSet.{u} ⥤ MarkedDiagSet.{u} ⥤ MarkedDiagSet.{u})
    (i : ∀ A, (F.obj markedTensorUnit).obj A ≅ A)
    (hi : ∀ {A B} (a : A ⟶ B), (F.obj markedTensorUnit).map a ≫ (i B).hom =
      (i A).hom ≫ a) {L A B : MarkedDiagSet.{u}}
    (x : markedTensorUnit ⟶ L) (a : A ⟶ B) :
    ((i A).inv ≫ (F.map x).app A) ≫ (F.obj L).map a =
      a ≫ (i B).inv ≫ (F.map x).app B := by
  have h : (i A).inv ≫ (F.obj markedTensorUnit).map a = a ≫ (i B).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, hi]
  rw [Category.assoc, ← (F.map x).naturality a, ← Category.assoc, h, Category.assoc]

private theorem mem_marked_tensor_corner
    (F : MarkedDiagSet.{u} ⥤ MarkedDiagSet.{u} ⥤ MarkedDiagSet.{u})
    {L A B P Y : MarkedDiagSet.{u}} (a : A ⟶ B) [IsIso (forget.map a)]
    (i : P ⟶ (F.obj L).obj B) (j : (F.obj L).obj A ⟶ P)
    (hj : j ≫ i = (F.obj L).map a) (u : P ⟶ Y)
    (l : forget.obj ((F.obj L).obj B) ⟶ forget.obj Y) (hl : forget.map i ≫ l = forget.map u)
    {T V : Atom} (w : diagram B.underlying V)
    (cA : diagram A.underlying V → diagram ((F.obj L).obj A).underlying T)
    (cB : diagram B.underlying V → diagram ((F.obj L).obj B).underlying T)
    (hc : ∀ w₀, cA w₀ ∈ ((F.obj L).obj A).marked T)
    (hca : ∀ w₀, (forget.map ((F.obj L).map a)).app (op T) (cA w₀) =
      cB ((forget.map a).app (op V) w₀)) :
    l.app (op T) (cB w) ∈ Y.marked T := by
  obtain ⟨w₀, rfl⟩ : ∃ w₀ : diagram A.underlying V, (forget.map a).app (op V) w₀ = w :=
    ⟨_, congrArg (fun f => f.app (op V) w) (IsIso.inv_hom_id (forget.map a))⟩
  have h : forget.map ((F.obj L).map a) ≫ l = forget.map j ≫ forget.map u := by
    rw [← hj, Functor.map_comp, Category.assoc, hl]
  have he : l.app (op T) ((forget.map ((F.obj L).map a)).app (op T) (cA w₀)) =
      (forget.map u).app (op T) ((forget.map j).app (op T) (cA w₀)) :=
    ConcreteCategory.congr_hom (congr_app h (op T)) (cA w₀)
  have he' := (congrArg (l.app (op T)) (hca w₀).symm).trans he
  exact he' ▸ MarkedPresheaf.map_mem_marked u (MarkedPresheaf.map_mem_marked j (hc w₀))

private theorem mem_marked_tensorVertex_square
    (F : MarkedDiagSet.{u} ⥤ MarkedDiagSet.{u} ⥤ MarkedDiagSet.{u})
    (i : ∀ A, (F.obj markedTensorUnit).obj A ≅ A)
    (hi : ∀ {A B} (a : A ⟶ B), (F.obj markedTensorUnit).map a ≫ (i B).hom =
      (i A).hom ≫ a) {L A B P Y S : MarkedDiagSet.{u}}
    (a : A ⟶ B) [IsIso (forget.map a)] (y : Y ⟶ S) [HasLiftingProperty a y]
    (ι : P ⟶ (F.obj L).obj B) (j : (F.obj L).obj A ⟶ P)
    (hj : j ≫ ι = (F.obj L).map a)
    {u : P ⟶ Y} {v : (F.obj L).obj B ⟶ S} (csq : CommSq u ι y v)
    (l : forget.obj ((F.obj L).obj B) ⟶ forget.obj Y)
    (hl : forget.map ι ≫ l = forget.map u) (x : markedTensorUnit ⟶ L)
    {T : Atom} (w : diagram B.underlying T) (hw : w ∈ B.marked T) :
    l.app (op T) ((forget.map ((i B).inv ≫ (F.map x).app B)).app (op T) w) ∈
      Y.marked T := by
  have h : (((i A).inv ≫ (F.map x).app A) ≫ j) ≫ ι =
      a ≫ (i B).inv ≫ (F.map x).app B := by
    rw [Category.assoc, hj]
    exact tensorVertex_naturality F i hi x a
  exact mem_marked_of_entire_restriction a y ι csq l hl _ _ h w hw

private theorem exists_mem_marked_tensorVertex_of_unitor
    (F : MarkedDiagSet.{u} ⥤ MarkedDiagSet.{u} ⥤ MarkedDiagSet.{u})
    {L B : MarkedDiagSet.{u}} (i : (F.obj markedTensorUnit).obj B ≅ B)
    (x : markedTensorUnit ⟶ L) {T : Atom}
    (c : diagram ((F.obj markedTensorUnit).obj B).underlying T)
    (hc : c ∈ ((F.obj markedTensorUnit).obj B).marked T)
    (z : diagram ((F.obj L).obj B).underlying T)
    (hz : (forget.map ((F.map x).app B)).app (op T) c = z) :
    ∃ w ∈ B.marked T,
      (forget.map (i.inv ≫ (F.map x).app B)).app (op T) w = z := by
  let w := (forget.map i.hom).app (op T) c
  refine ⟨w, MarkedPresheaf.map_mem_marked i.hom hc, ?_⟩
  have h : (forget.map (i.inv ≫ (F.map x).app B)).app (op T) w =
      (forget.map ((F.map x).app B)).app (op T) ((forget.map i.inv).app (op T) w) :=
    ConcreteCategory.congr_hom (congr_app (forget.map_comp _ _) (op T)) w
  exact h.trans ((congrArg ((forget.map ((F.map x).app B)).app (op T))
    (forget_map_inv_app_hom_app i c)).trans hz)

private theorem exists_vertex_of_dimension_eq_zero {L : MarkedDiagSet.{u}} {U : Atom}
    (x : diagram L.underlying U) (hU : U.dimension = 0) :
    ∃ xv : markedTensorUnit ⟶ L,
      (forget.map xv).app (op U) ⟨toAtomPoint U⟩ = x := by
  have := isIso_toAtomPoint_of_dimension_eq_zero hU
  let t : U ≅ atomPoint := asIso (toAtomPoint U)
  let xv : markedTensorUnit ⟶ L :=
    ((MarkedPresheaf.flatForgetAdjunction atomMarking).homEquiv _ L).symm
      (uliftYonedaEquiv.symm (L.underlying.map t.inv.op x))
  have hxvmap : forget.map xv =
      uliftYonedaEquiv.symm (L.underlying.map t.inv.op x) :=
    ((MarkedPresheaf.flatForgetAdjunction atomMarking).homEquiv _ L).apply_symm_apply _
  refine ⟨xv, ?_⟩
  rw [hxvmap]
  exact (L.underlying.map_comp_apply t.inv.op t.hom.op x).symm.trans (by
    rw [← op_comp, t.hom_inv_id, op_id, Functor.map_id_apply])

private theorem mem_marked_tensor_of_marked_factor
    (F : MarkedDiagSet.{u} ⥤ MarkedDiagSet.{u} ⥤ MarkedDiagSet.{u})
    {L B Y : MarkedDiagSet.{u}} (i : (F.obj markedTensorUnit).obj B ≅ B)
    (l : forget.obj ((F.obj L).obj B) ⟶ Y.underlying) {T U V : Atom}
    (x : diagram L.underlying U) (hV : 0 < V.dimension)
    (hdim : T.dimension = U.dimension + V.dimension)
    (c : ∀ X : MarkedDiagSet.{u}, diagram X.underlying U →
      diagram ((F.obj X).obj B).underlying T)
    (hc : ∀ q, c markedTensorUnit q ∈ ((F.obj markedTensorUnit).obj B).marked T)
    (hn : ∀ (xv : markedTensorUnit ⟶ L) q,
      (forget.map ((F.map xv).app B)).app (op T) (c markedTensorUnit q) =
        c L ((forget.map xv).app (op U) q))
    (hhi : 1 < T.dimension → l.app (op T) (c L x) ∈ Y.marked T)
    (hv : ∀ (xv : markedTensorUnit ⟶ L) (w : diagram B.underlying T),
      w ∈ B.marked T → l.app (op T)
        ((forget.map (i.inv ≫ (F.map xv).app B)).app (op T) w) ∈ Y.marked T) :
    l.app (op T) (c L x) ∈ Y.marked T := by
  by_cases hT : 1 < T.dimension
  · exact hhi hT
  have hU : U.dimension = 0 := by omega
  obtain ⟨xv, hxv⟩ := exists_vertex_of_dimension_eq_zero x hU
  obtain ⟨w, hw, he⟩ := exists_mem_marked_tensorVertex_of_unitor F i xv
    (c markedTensorUnit ⟨toAtomPoint U⟩) (hc _) (c L x)
    ((hn xv _).trans (congrArg (c L) hxv))
  rw [← he]
  exact hv xv w hw

theorem mem_marked_of_pushoutProduct_right {A B K L Y : MarkedDiagSet.{u}}
    (a : A ⟶ B) [IsIso (forget.map a)] {m : K ⟶ L}
    (sq : (Functor.curry.obj (markedTensorBifunctor.{u} false)).PushoutObjObj m a)
    (u : sq.pt ⟶ Y) (l : grayTensor L.underlying B.underlying ⟶ Y.underlying)
    (hl : forget.map sq.ι ≫ l = forget.map u)
    (hhi : ∀ (T : Atom) (z : diagram (grayTensor L.underlying B.underlying) T),
      1 < T.dimension → z ∈ (markedTensor false L B).marked T → l.app (op T) z ∈ Y.marked T)
    (hv : ∀ (xv : markedTensorUnit ⟶ L) (T : Atom) (w : diagram B.underlying T),
      w ∈ B.marked T → l.app (op T)
        ((forget.map ((markedTensorLeftUnitor false B).inv ≫
          markedTensorMap false xv (𝟙 B))).app (op T) w) ∈ Y.marked T)
    {T : Atom} (z : diagram (grayTensor L.underlying B.underlying) T)
    (hz : z ∈ (markedTensor false L B).marked T) : l.app (op T) z ∈ Y.marked T := by
  rcases (mem_marked_markedTensor _ _ _ _ _).1 hz with hd | ⟨U, V, x, w, e, hm, rfl⟩
  · exact Y.mem_marked_of_isDegenerate (isDegenerate_app l hd)
  rcases hm with hx | hw | ⟨h, -⟩
  · exact mem_marked_tensor_corner
      (Functor.curry.obj (markedTensorBifunctor false)) (L := L) a sq.ι sq.inl sq.inl_ι u l hl w
      (fun w₀ ↦ (grayTensor L.underlying A.underlying).map e.hom.op (grayTensorCell x w₀))
      (fun w₀ ↦ (grayTensor L.underlying B.underlying).map e.hom.op (grayTensorCell x w₀))
      (fun w₀ ↦ (mem_marked_markedTensor _ _ _ _ _).2
        (Or.inr ⟨U, V, x, w₀, e, Or.inl hx, rfl⟩))
      (fun w₀ ↦ forget_map_markedTensorMap_app false (𝟙 L) a e.hom x w₀)
  · exact mem_marked_tensor_of_marked_factor
      (Functor.curry.obj (markedTensorBifunctor false)) (markedTensorLeftUnitor false B)
      l x (B.markable V w hw)
      ((Atom.dimension_eq_of_iso e).trans (Atom.dimension_grayTensor U V))
      (fun X x ↦ (grayTensor X.underlying B.underlying).map e.hom.op (grayTensorCell x w))
      (fun q ↦ (mem_marked_markedTensor _ _ _ _ _).2
        (Or.inr ⟨U, V, q, w, e, Or.inr (Or.inl hw), rfl⟩))
      (fun xv q ↦ forget_map_markedTensorMap_app false xv (𝟙 B) e.hom q w)
      (fun hT ↦ hhi T _ hT hz) (fun xv w hw ↦ hv xv T w hw)
  · exact absurd h Bool.false_ne_true

theorem mem_marked_of_pushoutProduct_left {A B K L Y : MarkedDiagSet.{u}}
    (a : A ⟶ B) [IsIso (forget.map a)] {m : K ⟶ L}
    (sq : (Functor.curry.obj (markedTensorBifunctor.{u} false)).PushoutObjObj a m)
    (u : sq.pt ⟶ Y) (l : grayTensor B.underlying L.underlying ⟶ Y.underlying)
    (hl : forget.map sq.ι ≫ l = forget.map u)
    (hhi : ∀ (T : Atom) (z : diagram (grayTensor B.underlying L.underlying) T),
      1 < T.dimension → z ∈ (markedTensor false B L).marked T → l.app (op T) z ∈ Y.marked T)
    (hv : ∀ (xv : markedTensorUnit ⟶ L) (T : Atom) (w : diagram B.underlying T),
      w ∈ B.marked T → l.app (op T)
        ((forget.map ((markedTensorRightUnitor false B).inv ≫
          markedTensorMap false (𝟙 B) xv)).app (op T) w) ∈ Y.marked T)
    {T : Atom} (z : diagram (grayTensor B.underlying L.underlying) T)
    (hz : z ∈ (markedTensor false B L).marked T) : l.app (op T) z ∈ Y.marked T := by
  rcases (mem_marked_markedTensor _ _ _ _ _).1 hz with hd | ⟨U, V, w, x, e, hm, rfl⟩
  · exact Y.mem_marked_of_isDegenerate (isDegenerate_app l hd)
  rcases hm with hw | hx | ⟨h, -⟩
  · exact mem_marked_tensor_of_marked_factor
      (Functor.curry.obj (markedTensorBifunctor false)).flip (markedTensorRightUnitor false B)
      l x (B.markable U w hw)
      (by rw [Nat.add_comm]; exact
        (Atom.dimension_eq_of_iso e).trans (Atom.dimension_grayTensor U V))
      (fun X x ↦ (grayTensor B.underlying X.underlying).map e.hom.op (grayTensorCell w x))
      (fun q ↦ (mem_marked_markedTensor _ _ _ _ _).2
        (Or.inr ⟨U, V, w, q, e, Or.inl hw, rfl⟩))
      (fun xv q ↦ forget_map_markedTensorMap_app false (𝟙 B) xv e.hom w q)
      (fun hT ↦ hhi T _ hT hz) (fun xv w hw ↦ hv xv T w hw)
  · exact mem_marked_tensor_corner
      (Functor.curry.obj (markedTensorBifunctor false)).flip (L := L) a sq.ι sq.inr
      sq.inr_ι u l hl w
      (fun w₀ ↦ (grayTensor A.underlying L.underlying).map e.hom.op (grayTensorCell w₀ x))
      (fun w₀ ↦ (grayTensor B.underlying L.underlying).map e.hom.op (grayTensorCell w₀ x))
      (fun w₀ ↦ (mem_marked_markedTensor _ _ _ _ _).2
        (Or.inr ⟨U, V, w₀, x, e, Or.inr (Or.inl hx), rfl⟩))
      (fun w₀ ↦ forget_map_markedTensorMap_app false a (𝟙 L) e.hom w₀ x)
  · exact absurd h Bool.false_ne_true

private theorem hasLiftingProperty_of_tensorVertex
    (F : MarkedDiagSet.{u} ⥤ MarkedDiagSet.{u} ⥤ MarkedDiagSet.{u})
    (i : ∀ A, (F.obj markedTensorUnit).obj A ≅ A)
    (hi : ∀ {A B} (a : A ⟶ B), (F.obj markedTensorUnit).map a ≫ (i B).hom =
      (i A).hom ≫ a) {L A B P Y S : MarkedDiagSet.{u}}
    (a : A ⟶ B) [IsIso (forget.map a)] (y : Y ⟶ S)
    (hy : (markingGeneratorsAbove 1).rlp y) [HasLiftingProperty a y]
    (ι : P ⟶ (F.obj L).obj B) [IsIso (forget.map ι)]
    (j : (F.obj L).obj A ⟶ P) (hj : j ≫ ι = (F.obj L).map a)
    (h : ∀ (u : P ⟶ Y) (l : forget.obj ((F.obj L).obj B) ⟶ Y.underlying),
      forget.map ι ≫ l = forget.map u →
      (∀ (T : Atom) (z : diagram ((F.obj L).obj B).underlying T),
        1 < T.dimension → z ∈ ((F.obj L).obj B).marked T → l.app (op T) z ∈ Y.marked T) →
      (∀ (xv : markedTensorUnit ⟶ L) (T : Atom) (w : diagram B.underlying T),
        w ∈ B.marked T → l.app (op T)
          ((forget.map ((i B).inv ≫ (F.map xv).app B)).app (op T) w) ∈ Y.marked T) →
      ∀ (T : Atom) (z : diagram ((F.obj L).obj B).underlying T),
        z ∈ ((F.obj L).obj B).marked T → l.app (op T) z ∈ Y.marked T) :
    HasLiftingProperty ι y := by
  refine hasLiftingProperty_of_isIso_forget_of_mem_marked ι y ?_
  intro u v csq l hl hly
  exact h u l hl
    (fun T z hT hz ↦ mem_marked_of_rlp_markingGeneratorsAbove 1 y hy _
      (by exact_mod_cast hT) ((ConcreteCategory.congr_hom (congr_app hly (op T)) z) ▸
        MarkedPresheaf.map_mem_marked v hz))
    (fun xv T w hw ↦ mem_marked_tensorVertex_square F i hi
      (L := L) a y ι j hj csq l hl xv w hw)

theorem hasLiftingProperty_pushoutProduct_of_isIso_forget {K L A B Y S : MarkedDiagSet.{u}}
    (m : K ⟶ L) (a : A ⟶ B) [IsIso (forget.map a)] (y : Y ⟶ S)
    (hy : (markingGeneratorsAbove 1).rlp y) [HasLiftingProperty a y] :
    HasLiftingProperty (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) m a).ι y := by
  let sq := Functor.PushoutObjObj.ofHasPushout
    (Functor.curry.obj (markedTensorBifunctor.{u} false)) m a
  have : IsIso (forget.map sq.ι) := isIso_forget_map_pushoutProduct_right m a
  exact hasLiftingProperty_of_tensorVertex (L := L) (A := A) (B := B)
    (Functor.curry.obj (markedTensorBifunctor false))
    (markedTensorLeftUnitor false) (markedTensorLeftUnitor_naturality false)
    a y hy sq.ι sq.inl sq.inl_ι
    (fun u l hl hhi hv T z hz ↦ mem_marked_of_pushoutProduct_right
      a sq u l hl hhi hv z hz)

theorem hasLiftingProperty_pushoutProduct_of_isIso_forget_left {A B K L Y S : MarkedDiagSet.{u}}
    (a : A ⟶ B) [IsIso (forget.map a)] (m : K ⟶ L) (y : Y ⟶ S)
    (hy : (markingGeneratorsAbove 1).rlp y) [HasLiftingProperty a y] :
    HasLiftingProperty (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) a m).ι y := by
  let sq := Functor.PushoutObjObj.ofHasPushout
    (Functor.curry.obj (markedTensorBifunctor.{u} false)) a m
  have : IsIso (forget.map sq.ι) := isIso_forget_map_pushoutProduct_left a m
  exact hasLiftingProperty_of_tensorVertex (L := L) (A := A) (B := B)
    (Functor.curry.obj (markedTensorBifunctor false)).flip
    (markedTensorRightUnitor false) (markedTensorRightUnitor_naturality false)
    a y hy sq.ι sq.inr sq.inr_ι
    (fun u l hl hhi hv T z hz ↦ mem_marked_of_pushoutProduct_left
      a sq u l hl hhi hv z hz)

end Atoms.Diagrammatic
