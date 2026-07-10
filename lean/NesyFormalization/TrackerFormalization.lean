import NesyFormalization.NsiAgentFormalization

namespace EnvFormalization

/-!
  Tracker 层的抽象正确性引理。

  Python 实现里的 tracker 使用像素坐标、0.5px 怪物速度和 AABB 碰撞。
  本文件用半像素自然数坐标建模 tracker 的核心机制：关键帧同步会把不确定半径
  重置为 0，死推演期间 tracker 中心保持在上次观测位置，而真实怪物若每步位移
  不超过速度上界，则每步扩大的不确定球会持续覆盖真实位置。
-/

/-- 半像素单位的位置。`1` 表示 Python 中的 `0.5 px`。 -/
abbrev HalfPx := Nat

/-- 像素层位置的离散抽象，坐标单位是半像素。 -/
structure PixelPos where
  x : HalfPx
  y : HalfPx
  deriving Repr, DecidableEq, Inhabited

/-- 16px tile 在半像素单位下的长度。 -/
def halfTileSize : Nat := 32

/-- 怪物每步最多 0.5px，在半像素单位下就是 `1`。 -/
def halfMonsterSpeed : Nat := 1

/-- 像素层 Chebyshev 距离，用于描述 tracker 的方形不确定球。 -/
def pixelChebyshev (p q : PixelPos) : Nat :=
  Nat.max (absDiff p.x q.x) (absDiff p.y q.y)

/-- 真实位置 `real` 位于以 `center` 为中心、`radius` 为半径的不确定球内。 -/
def BallCovers (center : PixelPos) (radius : Nat) (real : PixelPos) : Prop :=
  pixelChebyshev real center ≤ radius

/-- 自然数绝对差满足三角不等式。 -/
theorem absDiff_triangle (a b c : Nat) :
    absDiff a c ≤ absDiff a b + absDiff b c := by
  unfold absDiff
  split <;> split <;> split <;> omega

/-- 绝对差的上界可以改写为两个方向的加法上界。 -/
theorem bounds_of_absDiff_le {a b n : Nat} (h : absDiff a b ≤ n) :
    a ≤ b + n ∧ b ≤ a + n := by
  unfold absDiff at h
  split at h <;> omega

/-- 像素层 Chebyshev 距离满足三角不等式。 -/
theorem pixelChebyshev_triangle (a b c : PixelPos) :
    pixelChebyshev a c ≤ pixelChebyshev a b + pixelChebyshev b c := by
  unfold pixelChebyshev
  rw [Nat.max_le]
  constructor
  · exact Nat.le_trans
      (absDiff_triangle a.x b.x c.x)
      (Nat.add_le_add (Nat.le_max_left _ _) (Nat.le_max_left _ _))
  · exact Nat.le_trans
      (absDiff_triangle a.y b.y c.y)
      (Nat.add_le_add (Nat.le_max_right _ _) (Nat.le_max_right _ _))

/-- 像素层 tracker 中的一只怪物：中心位置加不确定半径。 -/
structure PixelTrackedMonster where
  center : PixelPos
  uncertainty : Nat := 0
  deriving Repr, DecidableEq, Inhabited

/-- 关键帧同步：观测到怪物位置后，把中心更新为观测位置，并把不确定半径重置为 0。 -/
def syncMonster (observed : PixelPos) : PixelTrackedMonster :=
  { center := observed, uncertainty := 0 }

/-- 同步后的 tracker 怪物不确定半径为 0。 -/
theorem syncMonster_uncertainty_zero (observed : PixelPos) :
    (syncMonster observed).uncertainty = 0 := by
  rfl

/-- 若关键帧观测位置就是真实位置，则同步后的半径 0 不确定球覆盖真实怪物。 -/
theorem syncMonster_covers_observed (observed : PixelPos) :
    BallCovers (syncMonster observed).center (syncMonster observed).uncertainty observed := by
  simp [syncMonster, BallCovers, pixelChebyshev, absDiff]

/-- 一段 tracker 轨迹：预测中心、真实位置和不确定半径都随步数变化。 -/
structure TrackerBallTrace where
  center : Nat → PixelPos
  real : Nat → PixelPos
  radius : Nat → Nat

/-- tracker 每步按怪物速度上界扩大不确定半径。 -/
def RadiusGrowsBy (tr : TrackerBallTrace) (speed : Nat) : Prop :=
  ∀ t, tr.radius (t + 1) = tr.radius t + speed

/-- 死推演期间 tracker 中心保持在上次关键帧观测位置。 -/
def CenterStationary (tr : TrackerBallTrace) : Prop :=
  ∀ t, tr.center (t + 1) = tr.center t

/-- 真实怪物每一步的像素层 Chebyshev 位移不超过速度上界。 -/
def RealStepBounded (tr : TrackerBallTrace) (speed : Nat) : Prop :=
  ∀ t, pixelChebyshev (tr.real (t + 1)) (tr.real t) ≤ speed

/--
`tracker_ball_invariant`：如果关键帧时真实怪物在 tracker 不确定球内，死推演期间
tracker 中心不变、真实怪物每步位移不超过 `speed`，且半径每步按 `speed` 增长，
那么任意步数后真实位置仍在 tracker 的不确定球内。
-/
theorem tracker_ball_invariant
    (tr : TrackerBallTrace) (speed : Nat)
    (h0 : BallCovers (tr.center 0) (tr.radius 0) (tr.real 0))
    (hcenter : CenterStationary tr)
    (hgrow : RadiusGrowsBy tr speed)
    (hstep : RealStepBounded tr speed) :
    ∀ t, BallCovers (tr.center t) (tr.radius t) (tr.real t) := by
  intro t
  induction t with
  | zero =>
      exact h0
  | succ t ih =>
      unfold BallCovers at ih ⊢
      rw [hgrow t]
      rw [hcenter t]
      exact Nat.le_trans
        (pixelChebyshev_triangle (tr.real (t + 1)) (tr.real t) (tr.center t))
        (by
          have hs := hstep t
          omega)

/-- tile 层预测移动：目标格在界内且不阻挡时移动，否则原地。 -/
def predictedTileMove (knownBlocking : Position → Bool) (p : Position) (d : Direction) : Position :=
  let target := facingTile p d
  if inBounds target && !knownBlocking target then target else p

/-- tile 层引擎移动的抽象：使用真实阻挡集做同样的格子级钳制。 -/
def engineTileMove (realBlocking : Position → Bool) (p : Position) (d : Direction) : Position :=
  let target := facingTile p d
  if inBounds target && !realBlocking target then target else p

/-- tracker 的已知阻挡集与真实环境阻挡集一致。 -/
def BlockingSetsAgree (knownBlocking realBlocking : Position → Bool) : Prop :=
  ∀ p, knownBlocking p = realBlocking p

/--
`predict_move_engine_consistent`：若 tracker 的阻挡集与真实墙体/阻挡集一致，则
tracker 的 tile 层预测移动与引擎的 tile 层移动结果一致。
-/
theorem predict_move_engine_consistent
    {knownBlocking realBlocking : Position → Bool}
    (hagree : BlockingSetsAgree knownBlocking realBlocking)
    (p : Position) (d : Direction) :
    predictedTileMove knownBlocking p d = engineTileMove realBlocking p d := by
  simp [predictedTileMove, engineTileMove, hagree (facingTile p d)]

/--
`blocked_feedback_sound`：对 `NsiAgentFormalization` 中的 reward 反馈更新函数，
如果上一动作是移动、tracker 记录了上一格，且可靠的 blocked feedback
保证该上一格就是当前真实位置，那么回退修正后的预测位置等于真实位置。
-/
theorem blocked_feedback_sound
    {s : NsiAgentState} {previous realPlayer : Position}
    (hmove : s.tracker.lastActionWasMove = true)
    (hprev : s.tracker.previousPlayer? = some previous)
    (hreliable : previous = realPlayer) :
    (applyRewardBlockedFeedback true s).world.player = realPlayer := by
  rw [← hreliable]
  simp [applyRewardBlockedFeedback, hmove, hprev]

/-- 半像素坐标所属的 tile 下标。 -/
def halfPxTileCoord (coord : HalfPx) : Nat :=
  coord / halfTileSize

/-- 像素层位置按中心归格得到 tile 坐标。 -/
def pixelToTile (p : PixelPos) : Position :=
  (halfPxTileCoord p.x, halfPxTileCoord p.y)

/-- 单轴坐标距离当前 tile 的两侧边界都超过 0.5px。 -/
def CoordAwayFromTileBoundary (coord : HalfPx) : Prop :=
  halfTileSize * halfPxTileCoord coord + 2 ≤ coord ∧
    coord + 1 < halfTileSize * (halfPxTileCoord coord + 1)

/--
远离 tile 边界的条件。这里以半像素为单位，要求 x/y 中心坐标
与当前 tile 的两侧边界都保留足以吸收 ±0.5px 误差的余量。
-/
def AwayFromTileBoundary (p : PixelPos) : Prop :=
  CoordAwayFromTileBoundary p.x ∧ CoordAwayFromTileBoundary p.y

/-- 两个中心坐标在 x/y 两轴上的误差都不超过 0.5px（一个半像素单位）。 -/
def WithinHalfPixel (predicted real : PixelPos) : Prop :=
  absDiff predicted.x real.x ≤ 1 ∧ absDiff predicted.y real.y ≤ 1

/-- tracker 使用的 player tile 计算：将半像素中心坐标按 tile 尺寸整除归格。 -/
def trackerPlayerTile (center : PixelPos) : Position :=
  pixelToTile center

/--
半像素坐标 `coord` 属于第 `tile` 个 tile 的引擎侧区间。
这里用半开区间 `[tile * 32, (tile + 1) * 32)` 表示 tile 归属。
-/
def CoordInTile (coord : HalfPx) (tile : Nat) : Prop :=
  halfTileSize * tile ≤ coord ∧ coord < halfTileSize * (tile + 1)

/-- 整除得到的 tile 下标确实包含原坐标。 -/
theorem halfPxTileCoord_interval (coord : HalfPx) :
    CoordInTile coord (halfPxTileCoord coord) := by
  unfold CoordInTile halfPxTileCoord
  constructor
  · exact Nat.mul_div_le coord halfTileSize
  · exact Nat.lt_mul_div_succ coord (by decide : 0 < halfTileSize)

/--
若预测坐标距离 tile 边界超过 0.5px，且真实坐标与预测坐标相差不超过
0.5px，则两个坐标整除 tile 尺寸后得到相同的 tile 下标。
-/
theorem halfPxTileCoord_stable
    {predicted real : HalfPx}
    (hclose : absDiff predicted real ≤ 1)
    (haway : CoordAwayFromTileBoundary predicted) :
    halfPxTileCoord predicted = halfPxTileCoord real := by
  unfold CoordAwayFromTileBoundary halfPxTileCoord halfTileSize at haway
  unfold halfPxTileCoord halfTileSize
  rcases haway with ⟨hlower, hupper⟩
  rcases bounds_of_absDiff_le hclose with ⟨hPredLe, hRealLe⟩
  clear hclose
  have hrealLower : (predicted / 32) * 32 ≤ real := by
    have hcombined : 32 * (predicted / 32) + 2 ≤ real + 1 :=
      Nat.le_trans hlower hPredLe
    have hplus : 32 * (predicted / 32) + 1 ≤ real + 1 :=
      Nat.le_trans (Nat.add_le_add_left (by decide : 1 ≤ 2) _) hcombined
    have h : 32 * (predicted / 32) ≤ real :=
      Nat.le_of_add_le_add_right hplus
    simpa [Nat.mul_comm] using h
  have hrealUpper : real < (predicted / 32 + 1) * 32 := by
    have h : real < 32 * (predicted / 32 + 1) :=
      Nat.lt_of_le_of_lt hRealLe hupper
    simpa [Nat.mul_comm] using h
  symm
  exact Nat.div_eq_of_lt_le hrealLower hrealUpper

/--
引擎侧 tile 归属关系：玩家中心的 x/y 半像素坐标分别落在对应 tile 的半开区间内。
-/
def EngineTileContains (center : PixelPos) (tile : Position) : Prop :=
  CoordInTile center.x tile.1 ∧ CoordInTile center.y tile.2

/--
`player_tile_consistent`：若 tracker 预测的玩家中心与真实中心的误差不超过
0.5px，且预测中心到 tile 边界的距离超过 0.5px，则 tracker 和引擎的
中心归格结果相同；真实中心也确实落在该 tile 的半开区间内。
-/
theorem player_tile_consistent
    {predictedCenter realCenter : PixelPos}
    (hclose : WithinHalfPixel predictedCenter realCenter)
    (haway : AwayFromTileBoundary predictedCenter) :
    trackerPlayerTile predictedCenter = pixelToTile realCenter ∧
      EngineTileContains realCenter (trackerPlayerTile predictedCenter) := by
  rcases hclose with ⟨hxclose, hyclose⟩
  rcases haway with ⟨hxAway, hyAway⟩
  have hx : halfPxTileCoord predictedCenter.x = halfPxTileCoord realCenter.x :=
    halfPxTileCoord_stable hxclose hxAway
  have hy : halfPxTileCoord predictedCenter.y = halfPxTileCoord realCenter.y :=
    halfPxTileCoord_stable hyclose hyAway
  constructor
  · simp [trackerPlayerTile, pixelToTile, hx, hy]
  · rw [show trackerPlayerTile predictedCenter = pixelToTile realCenter by
      simp [trackerPlayerTile, pixelToTile, hx, hy]]
    unfold EngineTileContains pixelToTile
    constructor <;> exact halfPxTileCoord_interval _

end EnvFormalization
