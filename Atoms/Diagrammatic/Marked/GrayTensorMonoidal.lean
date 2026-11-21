import Atoms.Diagrammatic.Marked.GrayTensorClosed
import Atoms.Diagrammatic.GrayTensor.Monoidal
import Atoms.Diagrammatic.GrayTensor.Cells
import Atoms.Diagrammatic.GrayTensor.PushoutProduct
import Atoms.ForMathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj

open CategoryTheory Limits Opposite Atoms.Shape Atoms.Homotopical

universe w w' u

namespace Atoms.Diagrammatic

attribute [local irreducible] grayTensorBifunctor GrayDiagSet.associator GrayDiagSet.leftUnitor
  GrayDiagSet.rightUnitor

private theorem grayTensorCell_map_left {X Y : DiagSet.{u}} {U U' V : Atom} (f : U ⟶ U')
    (x : diagram X U') (y : diagram Y V) :
    grayTensorCell (X.map f.op x) y =
      (grayTensor X Y).map (Atom.grayTensorMap f (𝟙 V)).op (grayTensorCell x y) := by
  rw [← grayTensorCell_restrict, op_id, Functor.map_id_apply]

private theorem grayTensorCell_map_right {X Y : DiagSet.{u}} {U V V' : Atom} (g : V ⟶ V')
    (x : diagram X U) (y : diagram Y V') :
    grayTensorCell x (Y.map g.op y) =
      (grayTensor X Y).map (Atom.grayTensorMap (𝟙 U) g).op (grayTensorCell x y) := by
  rw [← grayTensorCell_restrict, op_id, Functor.map_id_apply]

private theorem app_mem_marked_of_tensorMask {pseudo : Bool} {X Y W : MarkedDiagSet.{u}}
    (f : grayTensor X.underlying Y.underlying ⟶ W.underlying)
    (hf : ∀ (U V : Atom) (x : diagram X.underlying U) (y : diagram Y.underlying V),
      tensorMask pseudo X Y U V x y → f.app _ (grayTensorCell x y) ∈ W.marked _)
    {T : Atom} {z : diagram (grayTensor X.underlying Y.underlying) T}
    (hz : z ∈ (markedTensor pseudo X Y).marked T) : f.app (op T) z ∈ W.marked T := by
  rcases (mem_marked_markedTensor _ _ _ _ _).1 hz with hz | ⟨U, V, x, y, e, hm, rfl⟩
  · exact MarkedDiagSet.mem_marked_of_isDegenerate W (isDegenerate_app f hz)
  · rw [NatTrans.naturality_apply]
    exact (W.transport e _).1 (hf U V x y hm)

private theorem grayTensorCell_mem_marked {pseudo : Bool} {X Y : MarkedDiagSet.{u}} {U V : Atom}
    {x : diagram X.underlying U} {y : diagram Y.underlying V} (h : tensorMask pseudo X Y U V x y) :
    grayTensorCell x y ∈ (markedTensor pseudo X Y).marked (Atom.grayTensor U V) :=
  (mem_marked_markedTensor _ _ _ _ _).2
    (Or.inr ⟨U, V, x, y, Iso.refl _, h, by rw [Iso.refl_hom, op_id, Functor.map_id_apply]⟩)

private theorem isDegenerate_or_exists_presentation (pseudo : Bool) (X Y : MarkedDiagSet.{u})
    {T : Atom} (t : diagram (grayTensor X.underlying Y.underlying) T) :
    IsDegenerate _ t ∨ ∃ (U V : Atom) (x : diagram X.underlying U) (y : diagram Y.underlying V)
      (e : T ≅ Atom.grayTensor U V),
      (t ∈ (markedTensor pseudo X Y).marked T → tensorMask pseudo X Y U V x y) ∧
      t = (grayTensor X.underlying Y.underlying).map e.hom.op (grayTensorCell x y) := by
  by_cases hd : IsDegenerate _ t
  · exact Or.inl hd
  by_cases hm : t ∈ (markedTensor pseudo X Y).marked T
  · rcases (mem_marked_markedTensor _ _ _ _ _).1 hm with h | ⟨U, V, x, y, e, hxy, rfl⟩
    · exact absurd h hd
    · exact Or.inr ⟨U, V, x, y, e, fun _ => hxy, rfl⟩
  · obtain ⟨U, V, x, y, e, -, -, rfl⟩ := exists_tensor_presentation t hd
    exact Or.inr ⟨U, V, x, y, e, fun h => absurd h hm, rfl⟩

private theorem associator_hom_app_mem_marked (pseudo : Bool) (X Y Z : MarkedDiagSet.{u})
    {T : Atom} {c : diagram (grayTensor (grayTensor X.underlying Y.underlying) Z.underlying) T}
    (hc : c ∈ (markedTensor pseudo (markedTensor pseudo X Y) Z).marked T) :
    (GrayDiagSet.associator X.underlying Y.underlying Z.underlying).hom.app _ c ∈
      (markedTensor pseudo X (markedTensor pseudo Y Z)).marked T := by
  refine app_mem_marked_of_tensorMask (pseudo := pseudo) (X := markedTensor pseudo X Y) (Y := Z)
    (W := markedTensor pseudo X (markedTensor pseudo Y Z))
    (GrayDiagSet.associator X.underlying Y.underlying Z.underlying).hom (fun A W t z hm => ?_) hc
  rcases isDegenerate_or_exists_presentation pseudo X Y t with ht | ⟨U, V, x, y, e, hxy, rfl⟩
  · exact MarkedDiagSet.mem_marked_of_isDegenerate _
      (isDegenerate_app _ (isDegenerate_grayTensorCell (Or.inl ht)))
  have hA := Atom.dimension_eq_of_iso e
  rw [Atom.dimension_grayTensor] at hA
  have key : (GrayDiagSet.associator X.underlying Y.underlying Z.underlying).hom.app _
      (grayTensorCell ((grayTensor X.underlying Y.underlying).map e.hom.op (grayTensorCell x y))
        z) = (grayTensor X.underlying (grayTensor Y.underlying Z.underlying)).map
        (MonoidalCategory.whiskerRightIso e W ≪≫ Atom.grayTensorAssoc U V W).hom.op
        (grayTensorCell x (grayTensorCell y z)) := by
    rw [grayTensorCell_map_left, NatTrans.naturality_apply,
      GrayDiagSet.associator_hom_app_grayTensorCell, ← Functor.map_comp_apply, ← op_comp]
    rfl
  refine (congrArg (· ∈ _) key).mpr ((MarkedPresheaf.transport _ _ _).1
    (grayTensorCell_mem_marked ?_))
  rcases hm with ht | hz | ⟨hp, hpA, hW⟩
  · rcases hxy ht with hx | hy | ⟨hp, hU, hV⟩
    · exact Or.inl hx
    · exact Or.inr (Or.inl (grayTensorCell_mem_marked (Or.inl hy)))
    · exact Or.inr (Or.inr ⟨hp, hU, by rw [Atom.dimension_grayTensor]; omega⟩)
  · exact Or.inr (Or.inl (grayTensorCell_mem_marked (Or.inr (Or.inl hz))))
  · by_cases hU : 0 < U.dimension
    · exact Or.inr (Or.inr ⟨hp, hU, by rw [Atom.dimension_grayTensor]; omega⟩)
    · exact Or.inr (Or.inl (grayTensorCell_mem_marked (Or.inr (Or.inr ⟨hp, by omega, hW⟩))))

private theorem associator_inv_app_mem_marked (pseudo : Bool) (X Y Z : MarkedDiagSet.{u})
    {T : Atom} {c : diagram (grayTensor X.underlying (grayTensor Y.underlying Z.underlying)) T}
    (hc : c ∈ (markedTensor pseudo X (markedTensor pseudo Y Z)).marked T) :
    (GrayDiagSet.associator X.underlying Y.underlying Z.underlying).inv.app _ c ∈
      (markedTensor pseudo (markedTensor pseudo X Y) Z).marked T := by
  refine app_mem_marked_of_tensorMask (pseudo := pseudo) (X := X) (Y := markedTensor pseudo Y Z)
    (W := markedTensor pseudo (markedTensor pseudo X Y) Z)
    (GrayDiagSet.associator X.underlying Y.underlying Z.underlying).inv (fun U A x s hm => ?_) hc
  rcases isDegenerate_or_exists_presentation pseudo Y Z s with hs | ⟨V, W, y, z, e, hyz, rfl⟩
  · exact MarkedDiagSet.mem_marked_of_isDegenerate _
      (isDegenerate_app _ (isDegenerate_grayTensorCell (Or.inr hs)))
  have hA := Atom.dimension_eq_of_iso e
  rw [Atom.dimension_grayTensor] at hA
  have key : (GrayDiagSet.associator X.underlying Y.underlying Z.underlying).inv.app _
      (grayTensorCell x ((grayTensor Y.underlying Z.underlying).map e.hom.op (grayTensorCell y z)))
        = (grayTensor (grayTensor X.underlying Y.underlying) Z.underlying).map
        (MonoidalCategory.whiskerLeftIso U e ≪≫ (Atom.grayTensorAssoc U V W).symm).hom.op
        (grayTensorCell (grayTensorCell x y) z) := by
    rw [grayTensorCell_map_right, NatTrans.naturality_apply,
      GrayDiagSet.associator_inv_app_grayTensorCell, ← Functor.map_comp_apply, ← op_comp]
    rfl
  refine (congrArg (· ∈ _) key).mpr ((MarkedPresheaf.transport _ _ _).1
    (grayTensorCell_mem_marked ?_))
  rcases hm with hx | hs | ⟨hp, hU, hpA⟩
  · exact Or.inl (grayTensorCell_mem_marked (Or.inl hx))
  · rcases hyz hs with hy | hz | ⟨hp, hV, hW⟩
    · exact Or.inl (grayTensorCell_mem_marked (Or.inr (Or.inl hy)))
    · exact Or.inr (Or.inl hz)
    · exact Or.inr (Or.inr ⟨hp, by rw [Atom.dimension_grayTensor]; omega, hW⟩)
  · by_cases hW : 0 < W.dimension
    · exact Or.inr (Or.inr ⟨hp, by rw [Atom.dimension_grayTensor]; omega, hW⟩)
    · exact Or.inl (grayTensorCell_mem_marked (Or.inr (Or.inr ⟨hp, hU, by omega⟩)))

private theorem map_mem_marked_of_isCollapseHom (X : MarkedDiagSet.{u}) {T U : Atom} {k : T ⟶ U}
    (hk : IsCollapseHom k) {x : diagram X.underlying U} (h : ¬ IsIso k ∨ x ∈ X.marked U) :
    X.underlying.map k.op x ∈ X.marked T := by
  by_cases hi : IsIso k
  · exact (X.transport (asIso k) x).1 (h.resolve_left (not_not.2 hi))
  · exact MarkedDiagSet.mem_marked_of_isDegenerate X ⟨U, k, x, hk, hi, rfl⟩

private theorem map_fst_mem_marked {pseudo : Bool} {X Y : MarkedDiagSet.{u}} {U V : Atom}
    {x : diagram X.underlying U} {y : diagram Y.underlying V} (hm : tensorMask pseudo X Y U V x y) :
    X.underlying.map (Atom.grayTensorMap (𝟙 U) (toAtomPoint V) ≫
      (Atom.grayTensorRightUnitor U).hom).op x ∈ X.marked _ := by
  refine map_mem_marked_of_isCollapseHom X (collapses.comp_mem _ _ (Atom.isCollapseHom_grayTensorMap
    _ _ (isCollapseHom_of_iso (Iso.refl U)) (isCollapseHom_toAtomPoint V))
    (isCollapseHom_of_iso _)) (or_iff_not_imp_left.2 fun hk => ?_)
  have hd := Atom.dimension_eq_of_iso (@asIso _ _ _ _ _ (not_not.1 hk))
  rw [Atom.dimension_grayTensor] at hd
  rcases hm with hx | hy | ⟨-, -, hV⟩
  · exact hx
  · have : 0 < V.dimension := Y.markable V y hy
    omega
  · omega

private theorem map_snd_mem_marked {pseudo : Bool} {X Y : MarkedDiagSet.{u}} {U V : Atom}
    {x : diagram X.underlying U} {y : diagram Y.underlying V} (hm : tensorMask pseudo X Y U V x y) :
    Y.underlying.map (Atom.grayTensorMap (toAtomPoint U) (𝟙 V) ≫
      (Atom.grayTensorLeftUnitor V).hom).op y ∈ Y.marked _ := by
  refine map_mem_marked_of_isCollapseHom Y (collapses.comp_mem _ _ (Atom.isCollapseHom_grayTensorMap
    _ _ (isCollapseHom_toAtomPoint U) (isCollapseHom_of_iso (Iso.refl V)))
    (isCollapseHom_of_iso _)) (or_iff_not_imp_left.2 fun hk => ?_)
  have hd := Atom.dimension_eq_of_iso (@asIso _ _ _ _ _ (not_not.1 hk))
  rw [Atom.dimension_grayTensor] at hd
  rcases hm with hx | hy | ⟨-, hU, -⟩
  · have : 0 < U.dimension := X.markable U x hx
    omega
  · exact hy
  · omega

noncomputable abbrev markedTensorUnit : MarkedDiagSet.{u} :=
  (MarkedPresheaf.flat atomMarking).obj (ball.{u} atomPoint)

noncomputable def isTerminalMarkedTensorUnit : IsTerminal markedTensorUnit.{u} :=
  IsTerminal.ofUniqueHom
    (fun X => MarkedPresheaf.homMk (isTerminalBallAtomPoint.from X.underlying) fun U x hx =>
      (MarkedDiagSet.mem_marked_flat_iff_isDegenerate _ U _).2 ⟨atomPoint, toAtomPoint U,
        ULift.up (𝟙 atomPoint), isCollapseHom_toAtomPoint U, fun hi => by
          have hd := Atom.dimension_eq_of_iso (@asIso _ _ _ _ _ hi)
          have : 0 < U.dimension := X.markable U x hx
          rw [dimension_atomPoint] at hd
          omega,
        ULift.ext _ _ (isTerminalAtomPoint.hom_ext _ _)⟩)
    fun _ _ => MarkedPresheaf.hom_ext (isTerminalBallAtomPoint.hom_ext _ _)

noncomputable def markedTensorLeftUnitor (pseudo : Bool) (X : MarkedDiagSet.{u}) :
    markedTensor pseudo markedTensorUnit X ≅ X where
  hom := MarkedPresheaf.homMk (GrayDiagSet.leftUnitor X.underlying).hom fun _ _ hc =>
    app_mem_marked_of_tensorMask (X := markedTensorUnit) (Y := X) (W := X)
      (GrayDiagSet.leftUnitor X.underlying).hom (fun _ _ p x hm =>
        (congrArg (· ∈ _) (GrayDiagSet.leftUnitor_hom_app_grayTensorCell p x)).mpr
          (map_snd_mem_marked hm)) hc
  inv := MarkedPresheaf.homMk (GrayDiagSet.leftUnitor X.underlying).inv fun U x hx => by
    let p : diagram (ball.{u} atomPoint) atomPoint := ULift.up (𝟙 atomPoint)
    have key : (GrayDiagSet.leftUnitor X.underlying).inv.app (op U) x =
        (grayTensor (ball atomPoint) X.underlying).map (Atom.grayTensorLeftUnitor U).inv.op
          (grayTensorCell p x) := by
      have h0 := GrayDiagSet.leftUnitor_hom_app_grayTensorCell (X := X.underlying) p x
      rw [isTerminalAtomPoint.hom_ext (toAtomPoint atomPoint) (𝟙 _), Atom.grayTensorMap_id,
        Category.id_comp] at h0
      conv_rhs => rw [← Iso.hom_inv_id_app_apply (GrayDiagSet.leftUnitor X.underlying) _
        (grayTensorCell p x), h0, ← NatTrans.naturality_apply, ← Functor.map_comp_apply,
        ← op_comp, Iso.inv_hom_id, op_id, Functor.map_id_apply]
    exact (congrArg (· ∈ _) key).mpr ((MarkedPresheaf.transport _
      (Atom.grayTensorLeftUnitor U).symm _).1 (grayTensorCell_mem_marked (Or.inr (Or.inl hx))))
  hom_inv_id := MarkedPresheaf.hom_ext (GrayDiagSet.leftUnitor X.underlying).hom_inv_id
  inv_hom_id := MarkedPresheaf.hom_ext (GrayDiagSet.leftUnitor X.underlying).inv_hom_id

noncomputable def markedTensorRightUnitor (pseudo : Bool) (X : MarkedDiagSet.{u}) :
    markedTensor pseudo X markedTensorUnit ≅ X where
  hom := MarkedPresheaf.homMk (GrayDiagSet.rightUnitor X.underlying).hom fun _ _ hc =>
    app_mem_marked_of_tensorMask (X := X) (Y := markedTensorUnit) (W := X)
      (GrayDiagSet.rightUnitor X.underlying).hom (fun _ _ x p hm =>
        (congrArg (· ∈ _) (GrayDiagSet.rightUnitor_hom_app_grayTensorCell x p)).mpr
          (map_fst_mem_marked hm)) hc
  inv := MarkedPresheaf.homMk (GrayDiagSet.rightUnitor X.underlying).inv fun U x hx => by
    let p : diagram (ball.{u} atomPoint) atomPoint := ULift.up (𝟙 atomPoint)
    have key : (GrayDiagSet.rightUnitor X.underlying).inv.app (op U) x =
        (grayTensor X.underlying (ball atomPoint)).map (Atom.grayTensorRightUnitor U).inv.op
          (grayTensorCell x p) := by
      have h0 := GrayDiagSet.rightUnitor_hom_app_grayTensorCell (X := X.underlying) x p
      rw [isTerminalAtomPoint.hom_ext (toAtomPoint atomPoint) (𝟙 _), Atom.grayTensorMap_id,
        Category.id_comp] at h0
      conv_rhs => rw [← Iso.hom_inv_id_app_apply (GrayDiagSet.rightUnitor X.underlying) _
        (grayTensorCell x p), h0, ← NatTrans.naturality_apply, ← Functor.map_comp_apply,
        ← op_comp, Iso.inv_hom_id, op_id, Functor.map_id_apply]
    exact (congrArg (· ∈ _) key).mpr ((MarkedPresheaf.transport _
      (Atom.grayTensorRightUnitor U).symm _).1 (grayTensorCell_mem_marked (Or.inl hx)))
  hom_inv_id := MarkedPresheaf.hom_ext (GrayDiagSet.rightUnitor X.underlying).hom_inv_id
  inv_hom_id := MarkedPresheaf.hom_ext (GrayDiagSet.rightUnitor X.underlying).inv_hom_id

noncomputable def markedTensorAssociator (pseudo : Bool) (X Y Z : MarkedDiagSet.{u}) :
    markedTensor pseudo (markedTensor pseudo X Y) Z ≅
      markedTensor pseudo X (markedTensor pseudo Y Z) where
  hom := MarkedPresheaf.homMk (GrayDiagSet.associator X.underlying Y.underlying Z.underlying).hom
    fun _ _ hc => associator_hom_app_mem_marked pseudo X Y Z hc
  inv := MarkedPresheaf.homMk (GrayDiagSet.associator X.underlying Y.underlying Z.underlying).inv
    fun _ _ hc => associator_inv_app_mem_marked pseudo X Y Z hc
  hom_inv_id := MarkedPresheaf.hom_ext (GrayDiagSet.associator _ _ _).hom_inv_id
  inv_hom_id := MarkedPresheaf.hom_ext (GrayDiagSet.associator _ _ _).inv_hom_id

@[simp] theorem forget_map_markedTensorAssociator_hom (pseudo : Bool) (X Y Z : MarkedDiagSet.{u}) :
    MarkedPresheaf.forget.map (markedTensorAssociator pseudo X Y Z).hom =
      (GrayDiagSet.associator X.underlying Y.underlying Z.underlying).hom :=
  rfl

@[simp] theorem forget_map_markedTensorAssociator_inv (pseudo : Bool) (X Y Z : MarkedDiagSet.{u}) :
    MarkedPresheaf.forget.map (markedTensorAssociator pseudo X Y Z).inv =
      (GrayDiagSet.associator X.underlying Y.underlying Z.underlying).inv :=
  rfl

@[simp] theorem forget_map_markedTensorLeftUnitor_hom (pseudo : Bool) (X : MarkedDiagSet.{u}) :
    MarkedPresheaf.forget.map (markedTensorLeftUnitor pseudo X).hom =
      (GrayDiagSet.leftUnitor X.underlying).hom :=
  rfl

@[simp] theorem forget_map_markedTensorLeftUnitor_inv (pseudo : Bool) (X : MarkedDiagSet.{u}) :
    MarkedPresheaf.forget.map (markedTensorLeftUnitor pseudo X).inv =
      (GrayDiagSet.leftUnitor X.underlying).inv :=
  rfl

@[simp] theorem forget_map_markedTensorRightUnitor_hom (pseudo : Bool) (X : MarkedDiagSet.{u}) :
    MarkedPresheaf.forget.map (markedTensorRightUnitor pseudo X).hom =
      (GrayDiagSet.rightUnitor X.underlying).hom :=
  rfl

@[simp] theorem forget_map_markedTensorRightUnitor_inv (pseudo : Bool) (X : MarkedDiagSet.{u}) :
    MarkedPresheaf.forget.map (markedTensorRightUnitor pseudo X).inv =
      (GrayDiagSet.rightUnitor X.underlying).inv :=
  rfl

@[reassoc] theorem markedTensorAssociator_naturality (pseudo : Bool)
    {X Y Z X' Y' Z' : MarkedDiagSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    markedTensorMap pseudo (markedTensorMap pseudo f g) h ≫
        (markedTensorAssociator pseudo X' Y' Z').hom =
      (markedTensorAssociator pseudo X Y Z).hom ≫
        markedTensorMap pseudo f (markedTensorMap pseudo g h) :=
  MarkedPresheaf.hom_ext (by
    simp only [Functor.map_comp, forget_map_markedTensorMap,
      forget_map_markedTensorAssociator_hom]
    exact GrayDiagSet.associator_naturality _ _ _)

@[reassoc] theorem markedTensorLeftUnitor_naturality (pseudo : Bool) {X Y : MarkedDiagSet.{u}}
    (f : X ⟶ Y) :
    markedTensorMap pseudo (𝟙 markedTensorUnit) f ≫ (markedTensorLeftUnitor pseudo Y).hom =
      (markedTensorLeftUnitor pseudo X).hom ≫ f :=
  MarkedPresheaf.hom_ext (by
    simp only [Functor.map_comp, forget_map_markedTensorMap,
      forget_map_markedTensorLeftUnitor_hom]
    exact GrayDiagSet.leftUnitor_naturality _)

@[reassoc] theorem markedTensorRightUnitor_naturality (pseudo : Bool) {X Y : MarkedDiagSet.{u}}
    (f : X ⟶ Y) :
    markedTensorMap pseudo f (𝟙 markedTensorUnit) ≫ (markedTensorRightUnitor pseudo Y).hom =
      (markedTensorRightUnitor pseudo X).hom ≫ f :=
  MarkedPresheaf.hom_ext (by
    simp only [Functor.map_comp, forget_map_markedTensorMap,
      forget_map_markedTensorRightUnitor_hom]
    exact GrayDiagSet.rightUnitor_naturality _)

theorem markedTensor_pentagon (pseudo : Bool) (X Y Z W : MarkedDiagSet.{u}) :
    markedTensorMap pseudo (markedTensorAssociator pseudo X Y Z).hom (𝟙 W) ≫
        (markedTensorAssociator pseudo X (markedTensor pseudo Y Z) W).hom ≫
          markedTensorMap pseudo (𝟙 X) (markedTensorAssociator pseudo Y Z W).hom =
      (markedTensorAssociator pseudo (markedTensor pseudo X Y) Z W).hom ≫
        (markedTensorAssociator pseudo X Y (markedTensor pseudo Z W)).hom :=
  MarkedPresheaf.hom_ext (by
    simp only [Functor.map_comp, forget_map_markedTensorMap,
      forget_map_markedTensorAssociator_hom]
    exact GrayDiagSet.pentagon _ _ _ _)

theorem markedTensor_triangle (pseudo : Bool) (X Y : MarkedDiagSet.{u}) :
    (markedTensorAssociator pseudo X markedTensorUnit Y).hom ≫
        markedTensorMap pseudo (𝟙 X) (markedTensorLeftUnitor pseudo Y).hom =
      markedTensorMap pseudo (markedTensorRightUnitor pseudo X).hom (𝟙 Y) :=
  MarkedPresheaf.hom_ext (by
    simp only [Functor.map_comp, forget_map_markedTensorMap,
      forget_map_markedTensorAssociator_hom, forget_map_markedTensorLeftUnitor_hom,
      forget_map_markedTensorRightUnitor_hom]
    exact GrayDiagSet.triangle _ _)

noncomputable def markedTensorFst (pseudo : Bool) (X Y : MarkedDiagSet.{u}) :
    markedTensor pseudo X Y ⟶ X :=
  MarkedPresheaf.homMk (grayTensorFst X.underlying Y.underlying) fun _ _ hz =>
    app_mem_marked_of_tensorMask (X := X) (Y := Y) (W := X) _ (fun _ _ x y hm =>
      (congrArg (· ∈ _) (grayTensorFst_app_grayTensorCell x y)).mpr (map_fst_mem_marked hm)) hz

noncomputable def markedTensorSnd (pseudo : Bool) (X Y : MarkedDiagSet.{u}) :
    markedTensor pseudo X Y ⟶ Y :=
  MarkedPresheaf.homMk (grayTensorSnd X.underlying Y.underlying) fun _ _ hz =>
    app_mem_marked_of_tensorMask (X := X) (Y := Y) (W := Y) _ (fun _ _ x y hm =>
      (congrArg (· ∈ _) (grayTensorSnd_app_grayTensorCell x y)).mpr (map_snd_mem_marked hm)) hz

theorem tensorRight_map_markedTensorSnd {pseudo : Bool} {T T' : MarkedDiagSet.{u}} (k : T ⟶ T')
    (B : MarkedDiagSet.{u}) :
    (tensorRight pseudo B).map k ≫ markedTensorSnd pseudo T' B = markedTensorSnd pseudo T B :=
  MarkedPresheaf.hom_ext ((MarkedPresheaf.forget.map_comp _ _).trans
    ((grayTensorBifunctor_map_grayTensorSnd (MarkedPresheaf.forget.map k) (𝟙 _)).trans
      (Category.comp_id _)))

instance mono_markedTensorMap (pseudo : Bool) {X Y X' Y' : MarkedDiagSet.{u}} (f : X ⟶ X')
    (g : Y ⟶ Y') [Mono f] [Mono g] : Mono (markedTensorMap pseudo f g) :=
  have := (MarkedPresheaf.mono_iff f).1 ‹_›
  have := (MarkedPresheaf.mono_iff g).1 ‹_›
  (MarkedPresheaf.mono_iff _).2 (mono_grayTensorBifunctor_map (MarkedPresheaf.forget.map f)
    (MarkedPresheaf.forget.map g))

theorem mono_markedPushoutProduct {X₁ Y₁ X₂ Y₂ : MarkedDiagSet.{u}} (f₁ : X₁ ⟶ Y₁)
    (f₂ : X₂ ⟶ Y₂) [Mono f₁] [Mono f₂] :
    Mono (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) f₁ f₂).ι := by
  have := (MarkedPresheaf.mono_iff f₁).1 ‹_›
  have := (MarkedPresheaf.mono_iff f₂).1 ‹_›
  have h := mono_pushoutProduct (MarkedPresheaf.forget.map f₁) (MarkedPresheaf.forget.map f₂)
  refine (MarkedPresheaf.mono_iff _).2 ?_
  exact ((MorphismProperty.monomorphisms DiagSet.{u}).arrow_mk_iso_iff
    (Functor.PushoutObjObj.mapArrowIso (G₃ := MarkedPresheaf.forget)
      (Functor.PushoutObjObj.ofHasPushout _ f₁ f₂) (Functor.PushoutObjObj.ofHasPushout _ _ _)
      (F' := Functor.curry.obj grayTensorBifunctor.{u}) (Iso.refl _))).2 h

@[implicit_reducible] def MarkedTensorDiagSet (_ : Bool) : Type (u + 1) := MarkedDiagSet.{u}

abbrev GrayMarkedDiagSet : Type (u + 1) := MarkedTensorDiagSet.{u} false

abbrev PseudoGrayMarkedDiagSet : Type (u + 1) := MarkedTensorDiagSet.{u} true

namespace MarkedTensorDiagSet

instance (pseudo : Bool) : Category.{u} (MarkedTensorDiagSet.{u} pseudo) :=
  inferInstanceAs (Category MarkedDiagSet.{u})

def toTensor (pseudo : Bool) : MarkedDiagSet.{u} ⥤ MarkedTensorDiagSet.{u} pseudo := 𝟭 _

def ofTensor (pseudo : Bool) : MarkedTensorDiagSet.{u} pseudo ⥤ MarkedDiagSet.{u} := 𝟭 _

@[simp] theorem ofTensor_obj_toTensor_obj (pseudo : Bool) (X : MarkedDiagSet.{u}) :
    (ofTensor pseudo).obj ((toTensor pseudo).obj X) = X :=
  rfl

@[simp] theorem ofTensor_map_toTensor_map (pseudo : Bool) {X Y : MarkedDiagSet.{u}} (f : X ⟶ Y) :
    (ofTensor pseudo).map ((toTensor pseudo).map f) = f :=
  rfl

@[simp] theorem toTensor_obj_ofTensor_obj (pseudo : Bool) (X : MarkedTensorDiagSet.{u} pseudo) :
    (toTensor pseudo).obj ((ofTensor pseudo).obj X) = X :=
  rfl

@[simp] theorem toTensor_map_ofTensor_map (pseudo : Bool) {X Y : MarkedTensorDiagSet.{u} pseudo}
    (f : X ⟶ Y) : (toTensor pseudo).map ((ofTensor pseudo).map f) = f :=
  rfl

def equivalence (pseudo : Bool) : MarkedTensorDiagSet.{u} pseudo ≌ MarkedDiagSet.{u} where
  functor := ofTensor pseudo
  inverse := toTensor pseudo
  unitIso := Iso.refl _
  counitIso := Iso.refl _

instance (pseudo : Bool) : (ofTensor.{u} pseudo).IsEquivalence :=
  (equivalence pseudo).isEquivalence_functor

instance (pseudo : Bool) : HasColimits (MarkedTensorDiagSet.{u} pseudo) :=
  inferInstanceAs (HasColimits MarkedDiagSet.{u})

open MonoidalCategory

noncomputable instance instMonoidalCategory (pseudo : Bool) :
    MonoidalCategory (MarkedTensorDiagSet.{u} pseudo) :=
  letI : MonoidalCategoryStruct (MarkedTensorDiagSet.{u} pseudo) :=
    { tensorObj := fun X Y => (toTensor pseudo).obj
        (markedTensor pseudo ((ofTensor pseudo).obj X) ((ofTensor pseudo).obj Y))
      whiskerLeft := fun X _ _ g => (toTensor pseudo).map
        (markedTensorMap pseudo (𝟙 ((ofTensor pseudo).obj X)) ((ofTensor pseudo).map g))
      whiskerRight := fun f Y => (toTensor pseudo).map
        (markedTensorMap pseudo ((ofTensor pseudo).map f) (𝟙 ((ofTensor pseudo).obj Y)))
      tensorHom := fun f g => (toTensor pseudo).map
        (markedTensorMap pseudo ((ofTensor pseudo).map f) ((ofTensor pseudo).map g))
      tensorUnit := (toTensor pseudo).obj markedTensorUnit
      associator := fun X Y Z => (toTensor pseudo).mapIso (markedTensorAssociator pseudo
        ((ofTensor pseudo).obj X) ((ofTensor pseudo).obj Y) ((ofTensor pseudo).obj Z))
      leftUnitor := fun X =>
        (toTensor pseudo).mapIso (markedTensorLeftUnitor pseudo ((ofTensor pseudo).obj X))
      rightUnitor := fun X =>
        (toTensor pseudo).mapIso (markedTensorRightUnitor pseudo ((ofTensor pseudo).obj X)) }
  .ofTensorHom
    (id_tensorHom_id := fun X Y => (markedTensorBifunctor pseudo).map_id (X, Y))
    (id_tensorHom := fun _ _ _ _ => rfl)
    (tensorHom_id := fun _ _ => rfl)
    (tensorHom_comp_tensorHom := fun f₁ f₂ g₁ g₂ =>
      ((markedTensorBifunctor pseudo).map_comp (X := (_, _)) (Y := (_, _)) (Z := (_, _))
        (f₁, f₂) (g₁, g₂)).symm)
    (associator_naturality := markedTensorAssociator_naturality pseudo)
    (leftUnitor_naturality := markedTensorLeftUnitor_naturality pseudo)
    (rightUnitor_naturality := markedTensorRightUnitor_naturality pseudo)
    (pentagon := markedTensor_pentagon pseudo)
    (triangle := markedTensor_triangle pseudo)

@[simp] theorem ofTensor_obj_tensorObj (pseudo : Bool) (X Y : MarkedTensorDiagSet.{u} pseudo) :
    (ofTensor pseudo).obj (X ⊗ Y) =
      markedTensor pseudo ((ofTensor pseudo).obj X) ((ofTensor pseudo).obj Y) :=
  rfl

@[simp] theorem ofTensor_obj_tensorUnit (pseudo : Bool) :
    (ofTensor pseudo).obj (𝟙_ (MarkedTensorDiagSet.{u} pseudo)) = markedTensorUnit :=
  rfl

@[simp] theorem ofTensor_map_tensorHom (pseudo : Bool) {X Y X' Y' : MarkedTensorDiagSet.{u} pseudo}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (ofTensor pseudo).map (f ⊗ₘ g) =
      markedTensorMap pseudo ((ofTensor pseudo).map f) ((ofTensor pseudo).map g) :=
  rfl

@[simp] theorem ofTensor_map_whiskerLeft (pseudo : Bool) (X : MarkedTensorDiagSet.{u} pseudo)
    {Y Y' : MarkedTensorDiagSet.{u} pseudo} (g : Y ⟶ Y') :
    (ofTensor pseudo).map (X ◁ g) =
      markedTensorMap pseudo (𝟙 ((ofTensor pseudo).obj X)) ((ofTensor pseudo).map g) :=
  rfl

@[simp] theorem ofTensor_map_whiskerRight (pseudo : Bool) {X X' : MarkedTensorDiagSet.{u} pseudo}
    (f : X ⟶ X') (Y : MarkedTensorDiagSet.{u} pseudo) :
    (ofTensor pseudo).map (f ▷ Y) =
      markedTensorMap pseudo ((ofTensor pseudo).map f) (𝟙 ((ofTensor pseudo).obj Y)) :=
  rfl

@[simp] theorem ofTensor_map_associator_hom (pseudo : Bool)
    (X Y Z : MarkedTensorDiagSet.{u} pseudo) :
    (ofTensor pseudo).map (α_ X Y Z).hom = (markedTensorAssociator pseudo
      ((ofTensor pseudo).obj X) ((ofTensor pseudo).obj Y) ((ofTensor pseudo).obj Z)).hom :=
  rfl

@[simp] theorem ofTensor_map_associator_inv (pseudo : Bool)
    (X Y Z : MarkedTensorDiagSet.{u} pseudo) :
    (ofTensor pseudo).map (α_ X Y Z).inv = (markedTensorAssociator pseudo
      ((ofTensor pseudo).obj X) ((ofTensor pseudo).obj Y) ((ofTensor pseudo).obj Z)).inv :=
  rfl

@[simp] theorem ofTensor_map_leftUnitor_hom (pseudo : Bool) (X : MarkedTensorDiagSet.{u} pseudo) :
    (ofTensor pseudo).map (λ_ X).hom =
      (markedTensorLeftUnitor pseudo ((ofTensor pseudo).obj X)).hom :=
  rfl

@[simp] theorem ofTensor_map_leftUnitor_inv (pseudo : Bool) (X : MarkedTensorDiagSet.{u} pseudo) :
    (ofTensor pseudo).map (λ_ X).inv =
      (markedTensorLeftUnitor pseudo ((ofTensor pseudo).obj X)).inv :=
  rfl

@[simp] theorem ofTensor_map_rightUnitor_hom (pseudo : Bool) (X : MarkedTensorDiagSet.{u} pseudo) :
    (ofTensor pseudo).map (ρ_ X).hom =
      (markedTensorRightUnitor pseudo ((ofTensor pseudo).obj X)).hom :=
  rfl

@[simp] theorem ofTensor_map_rightUnitor_inv (pseudo : Bool) (X : MarkedTensorDiagSet.{u} pseudo) :
    (ofTensor pseudo).map (ρ_ X).inv =
      (markedTensorRightUnitor pseudo ((ofTensor pseudo).obj X)).inv :=
  rfl

noncomputable instance (pseudo : Bool) :
    SemiCartesianMonoidalCategory (MarkedTensorDiagSet.{u} pseudo) :=
  { instMonoidalCategory pseudo with
    isTerminalTensorUnit := isTerminalMarkedTensorUnit
    fst := fun X Y => (toTensor pseudo).map
      (markedTensorFst pseudo ((ofTensor pseudo).obj X) ((ofTensor pseudo).obj Y))
    snd := fun X Y => (toTensor pseudo).map
      (markedTensorSnd pseudo ((ofTensor pseudo).obj X) ((ofTensor pseudo).obj Y))
    fst_def := fun _ _ => MarkedPresheaf.hom_ext rfl
    snd_def := fun _ _ => MarkedPresheaf.hom_ext rfl }

@[simp] theorem ofTensor_map_fst (pseudo : Bool) (X Y : MarkedTensorDiagSet.{u} pseudo) :
    (ofTensor pseudo).map (SemiCartesianMonoidalCategory.fst X Y) =
      markedTensorFst pseudo ((ofTensor pseudo).obj X) ((ofTensor pseudo).obj Y) :=
  rfl

@[simp] theorem ofTensor_map_snd (pseudo : Bool) (X Y : MarkedTensorDiagSet.{u} pseudo) :
    (ofTensor pseudo).map (SemiCartesianMonoidalCategory.snd X Y) =
      markedTensorSnd pseudo ((ofTensor pseudo).obj X) ((ofTensor pseudo).obj Y) :=
  rfl

instance (pseudo : Bool) (X : MarkedTensorDiagSet.{u} pseudo) :
    PreservesColimitsOfSize.{w, w'} (MonoidalCategory.tensorLeft X) :=
  inferInstanceAs (PreservesColimitsOfSize.{w, w'} (tensorLeft pseudo ((ofTensor pseudo).obj X)))

instance (pseudo : Bool) (X : MarkedTensorDiagSet.{u} pseudo) :
    PreservesColimitsOfSize.{w, w'} (MonoidalCategory.tensorRight X) :=
  inferInstanceAs (PreservesColimitsOfSize.{w, w'} (tensorRight pseudo ((ofTensor pseudo).obj X)))

noncomputable instance (pseudo : Bool) : MonoidalClosed (MarkedTensorDiagSet.{u} pseudo) where
  closed X :=
    { rightAdj := markedHomLeft pseudo ((ofTensor pseudo).obj X)
      adj := tensorLeftAdjunction pseudo ((ofTensor pseudo).obj X) }

noncomputable def forget (pseudo : Bool) : MarkedTensorDiagSet.{u} pseudo ⥤ GrayDiagSet.{u} :=
  ofTensor pseudo ⋙ MarkedPresheaf.forget ⋙ GrayDiagSet.toGray

noncomputable instance (pseudo : Bool) : (forget.{u} pseudo).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso _ _ := Iso.refl _
      μIso_hom_natural_left _ _ := (Category.comp_id _).trans (Category.id_comp _).symm
      μIso_hom_natural_right _ _ := (Category.comp_id _).trans (Category.id_comp _).symm
      associativity X Y Z := by
        refine (congrArg (· ≫ _) (id_whiskerRight
          ((forget pseudo).obj X ⊗ (forget pseudo).obj Y) ((forget pseudo).obj Z))).trans ?_
        refine Eq.trans ?_ (congrArg (_ ≫ ·) (congrArg (· ≫ _) (MonoidalCategory.whiskerLeft_id
          ((forget pseudo).obj X) ((forget pseudo).obj Y ⊗ (forget pseudo).obj Z)))).symm
        exact (Category.id_comp _).trans ((Category.id_comp _).trans (by rfl))
      left_unitality X := by
        refine Eq.trans ?_ (congrArg (· ≫ _)
          (id_whiskerRight (𝟙_ GrayDiagSet.{u}) ((forget pseudo).obj X))).symm
        exact ((Category.id_comp _).trans (Category.id_comp _)).symm
      right_unitality X := by
        refine Eq.trans ?_ (congrArg (· ≫ _)
          (MonoidalCategory.whiskerLeft_id ((forget pseudo).obj X) (𝟙_ GrayDiagSet.{u}))).symm
        exact ((Category.id_comp _).trans (Category.id_comp _)).symm }

private theorem grayTensorBifunctor_map_id_id (X Y : DiagSet.{u}) :
    grayTensorBifunctor.map (𝟙 X, 𝟙 Y) = 𝟙 (grayTensor X Y) :=
  grayTensorBifunctor.map_id (X, Y)

noncomputable def flat : GrayDiagSet.{u} ⥤ GrayMarkedDiagSet.{u} :=
  GrayDiagSet.ofGray ⋙ MarkedPresheaf.flat atomMarking ⋙ toTensor false

noncomputable instance : flat.{u}.Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso X Y := (toTensor false).mapIso
        (markedTensorFlatIso (GrayDiagSet.ofGray.obj X) (GrayDiagSet.ofGray.obj Y))
      μIso_hom_natural_left {A B} f X := by
        have e : grayTensorBifunctor.map (X := (GrayDiagSet.ofGray.obj A, GrayDiagSet.ofGray.obj X))
            (Y := (GrayDiagSet.ofGray.obj B, GrayDiagSet.ofGray.obj X))
            (GrayDiagSet.ofGray.map f, 𝟙 _) ≫ 𝟙 _ = 𝟙 _ ≫ grayTensorBifunctor.map
              (X := (GrayDiagSet.ofGray.obj A, GrayDiagSet.ofGray.obj X))
              (Y := (GrayDiagSet.ofGray.obj B, GrayDiagSet.ofGray.obj X))
              (GrayDiagSet.ofGray.map f, 𝟙 _) :=
          (Category.comp_id _).trans (Category.id_comp _).symm
        exact MarkedPresheaf.hom_ext e
      μIso_hom_natural_right {A B} X f := by
        have e : grayTensorBifunctor.map (X := (GrayDiagSet.ofGray.obj X, GrayDiagSet.ofGray.obj A))
            (Y := (GrayDiagSet.ofGray.obj X, GrayDiagSet.ofGray.obj B))
            (𝟙 _, GrayDiagSet.ofGray.map f) ≫ 𝟙 _ = 𝟙 _ ≫ grayTensorBifunctor.map
              (X := (GrayDiagSet.ofGray.obj X, GrayDiagSet.ofGray.obj A))
              (Y := (GrayDiagSet.ofGray.obj X, GrayDiagSet.ofGray.obj B))
              (𝟙 _, GrayDiagSet.ofGray.map f) :=
          (Category.comp_id _).trans (Category.id_comp _).symm
        exact MarkedPresheaf.hom_ext e
      associativity X Y Z := by
        have e : grayTensorBifunctor.map (𝟙 (grayTensor (GrayDiagSet.ofGray.obj X)
            (GrayDiagSet.ofGray.obj Y)), 𝟙 (GrayDiagSet.ofGray.obj Z)) ≫ 𝟙 _ ≫
              (GrayDiagSet.associator (GrayDiagSet.ofGray.obj X) (GrayDiagSet.ofGray.obj Y)
                (GrayDiagSet.ofGray.obj Z)).hom =
            (GrayDiagSet.associator (GrayDiagSet.ofGray.obj X) (GrayDiagSet.ofGray.obj Y)
              (GrayDiagSet.ofGray.obj Z)).hom ≫ grayTensorBifunctor.map
                (𝟙 (GrayDiagSet.ofGray.obj X), 𝟙 (grayTensor (GrayDiagSet.ofGray.obj Y)
                  (GrayDiagSet.ofGray.obj Z))) ≫ 𝟙 _ := by
          rw [grayTensorBifunctor_map_id_id, grayTensorBifunctor_map_id_id]
          simp only [Category.id_comp, Category.comp_id]
        exact MarkedPresheaf.hom_ext e
      left_unitality X := by
        have e : (GrayDiagSet.leftUnitor (GrayDiagSet.ofGray.obj X)).hom =
            grayTensorBifunctor.map (𝟙 (ball atomPoint), 𝟙 (GrayDiagSet.ofGray.obj X)) ≫ 𝟙 _ ≫
              (GrayDiagSet.leftUnitor (GrayDiagSet.ofGray.obj X)).hom := by
          rw [grayTensorBifunctor_map_id_id, Category.id_comp, Category.id_comp]
        exact MarkedPresheaf.hom_ext e
      right_unitality X := by
        have e : (GrayDiagSet.rightUnitor (GrayDiagSet.ofGray.obj X)).hom =
            grayTensorBifunctor.map (𝟙 (GrayDiagSet.ofGray.obj X), 𝟙 (ball atomPoint)) ≫ 𝟙 _ ≫
              (GrayDiagSet.rightUnitor (GrayDiagSet.ofGray.obj X)).hom := by
          rw [grayTensorBifunctor_map_id_id, Category.id_comp, Category.id_comp]
        exact MarkedPresheaf.hom_ext e }

noncomputable def grayToPseudoFunctor : GrayMarkedDiagSet.{u} ⥤ PseudoGrayMarkedDiagSet.{u} :=
  ofTensor false ⋙ toTensor true

noncomputable instance : grayToPseudoFunctor.{u}.OplaxMonoidal where
  η := 𝟙 _
  δ X Y := (toTensor true).map (grayToPseudo ((ofTensor false).obj X) ((ofTensor false).obj Y))
  δ_natural_left f _ := (grayToPseudo_naturality _ _).symm
  δ_natural_right _ f := (grayToPseudo_naturality _ _).symm
  oplax_associativity X Y Z := by
    let A := ((ofTensor false).obj X).underlying
    let B := ((ofTensor false).obj Y).underlying
    let C := ((ofTensor false).obj Z).underlying
    have e : 𝟙 _ ≫ grayTensorBifunctor.map (𝟙 (grayTensor A B), 𝟙 C) ≫
          (GrayDiagSet.associator A B C).hom =
        (GrayDiagSet.associator A B C).hom ≫ 𝟙 _ ≫
          grayTensorBifunctor.map (𝟙 A, 𝟙 (grayTensor B C)) := by
      rw [grayTensorBifunctor_map_id_id, grayTensorBifunctor_map_id_id]
      simp only [Category.id_comp, Category.comp_id]
    exact MarkedPresheaf.hom_ext e
  oplax_left_unitality X := by
    let A := ((ofTensor false).obj X).underlying
    have e : (GrayDiagSet.leftUnitor A).inv =
        (GrayDiagSet.leftUnitor A).inv ≫ 𝟙 _ ≫
          grayTensorBifunctor.map (𝟙 (ball atomPoint), 𝟙 A) := by
      rw [grayTensorBifunctor_map_id_id]
      simp only [Category.comp_id]
    exact MarkedPresheaf.hom_ext e
  oplax_right_unitality X := by
    let A := ((ofTensor false).obj X).underlying
    have e : (GrayDiagSet.rightUnitor A).inv =
        (GrayDiagSet.rightUnitor A).inv ≫ 𝟙 _ ≫
          grayTensorBifunctor.map (𝟙 A, 𝟙 (ball atomPoint)) := by
      rw [grayTensorBifunctor_map_id_id]
      simp only [Category.comp_id]
    exact MarkedPresheaf.hom_ext e

@[simp] theorem grayToPseudoFunctor_δ (X Y : GrayMarkedDiagSet.{u}) :
    Functor.OplaxMonoidal.δ grayToPseudoFunctor X Y =
      (toTensor true).map (grayToPseudo ((ofTensor false).obj X) ((ofTensor false).obj Y)) :=
  rfl

end MarkedTensorDiagSet

end Atoms.Diagrammatic
