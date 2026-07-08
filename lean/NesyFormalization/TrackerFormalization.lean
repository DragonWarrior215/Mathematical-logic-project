import NesyFormalization.NsiAgentFormalization

namespace EnvFormalization

/-!
  Tracker 层的抽象正确性引理。

  Python 实现里的 tracker 使用像素坐标、0.5px 怪物速度和 AABB 碰撞。
  本文件不直接形式化浮点和完整碰撞盒，而是把这些实现细节压缩成几个
  可检查的符号接口条件，然后证明它们足以推出报告中列出的 tracker 性质。
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

/--
每一步真实怪物的新位置都落在“上一半径加速度上界”的覆盖范围内。

在完整像素模型中，这个条件可由“怪物每步位移不超过 `speed`”以及 tracker
中心的更新规则推出；这里把它作为死推演层的局部接口。
-/
def RealStepWithinGrowth (tr : TrackerBallTrace) (speed : Nat) : Prop :=
  ∀ t, BallCovers (tr.center (t + 1)) (tr.radius t + speed) (tr.real (t + 1))

/--
`tracker_ball_invariant`：如果关键帧时真实怪物在 tracker 不确定球内，且之后每步
半径按速度上界增长、真实位置满足局部覆盖条件，那么任意步数后真实位置仍在球内。
-/
theorem tracker_ball_invariant
    (tr : TrackerBallTrace) (speed : Nat)
    (h0 : BallCovers (tr.center 0) (tr.radius 0) (tr.real 0))
    (hgrow : RadiusGrowsBy tr speed)
    (hstep : RealStepWithinGrowth tr speed) :
    ∀ t, BallCovers (tr.center t) (tr.radius t) (tr.real t) := by
  intro t
  induction t with
  | zero =>
      exact h0
  | succ t _ih =>
      rw [hgrow t]
      exact hstep t

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
invalid-action 反馈后的回退修正。若上一动作是移动且反馈说明撞墙，则回到上一位置；
否则保留当前预测位置。
-/
def applyBlockedFeedback
    (previous predicted : PixelPos) (lastActionWasMove invalidFeedback : Bool) : PixelPos :=
  if lastActionWasMove && invalidFeedback then previous else predicted

/--
`blocked_feedback_sound`：若 invalid-action 反馈可靠地说明真实玩家停在上一位置，
则回退修正后的 tracker 预测位置等于真实位置。
-/
theorem blocked_feedback_sound
    {previous predicted real : PixelPos}
    (hreliable : real = previous) :
    applyBlockedFeedback previous predicted true true = real := by
  simp [applyBlockedFeedback, hreliable]

/-- 半像素坐标所属的 tile 下标。 -/
def halfPxTileCoord (coord : HalfPx) : Nat :=
  coord / halfTileSize

/-- 像素层位置按中心归格得到 tile 坐标。 -/
def pixelToTile (p : PixelPos) : Position :=
  (halfPxTileCoord p.x, halfPxTileCoord p.y)

/--
远离 tile 边界的条件。这里以半像素为单位排除边界及其相邻半像素点，表示
中心点没有落在可能需要 disambiguation 的边界区域。
-/
def AwayFromTileBoundary (p : PixelPos) : Prop :=
  p.x % halfTileSize ≠ 0 ∧
  p.x % halfTileSize ≠ 1 ∧
  p.x % halfTileSize ≠ halfTileSize - 1 ∧
  p.y % halfTileSize ≠ 0 ∧
  p.y % halfTileSize ≠ 1 ∧
  p.y % halfTileSize ≠ halfTileSize - 1

/-- tracker 使用的 player tile 计算。 -/
def trackerPlayerTile (center : PixelPos) : Position :=
  pixelToTile center

/-- 引擎公开信息中的 player tile 计算。 -/
def enginePlayerTile (center : PixelPos) : Position :=
  pixelToTile center

/--
`player_tile_consistent`：当中心点远离 tile 边界时，tracker 和引擎使用同一归格规则
得到的 player tile 一致。边界 disambiguation 不包含在这个保证里。
-/
theorem player_tile_consistent
    {center : PixelPos}
    (_haway : AwayFromTileBoundary center) :
    trackerPlayerTile center = enginePlayerTile center := by
  rfl

end EnvFormalization
