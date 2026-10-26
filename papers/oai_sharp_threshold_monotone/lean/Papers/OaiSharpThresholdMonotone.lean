module
public import Papers.OaiSharpThresholdMonotone.Basic
public import Papers.OaiSharpThresholdMonotone.Helpers
public import Papers.OaiSharpThresholdMonotone.Helpers.BlockAverage
public import Papers.OaiSharpThresholdMonotone.Helpers.BlockCapture
public import Papers.OaiSharpThresholdMonotone.Helpers.Capture
public import Papers.OaiSharpThresholdMonotone.Helpers.ConstantBounds
public import Papers.OaiSharpThresholdMonotone.Helpers.Fourier
public import Papers.OaiSharpThresholdMonotone.Helpers.LowDegree
public import Papers.OaiSharpThresholdMonotone.Helpers.NoiseBasics
public import Papers.OaiSharpThresholdMonotone.Helpers.NoiseOperator
public import Papers.OaiSharpThresholdMonotone.Helpers.NoiseTensorization
public import Papers.OaiSharpThresholdMonotone.Helpers.OrbitCounting
public import Papers.OaiSharpThresholdMonotone.Helpers.Restriction
public import Papers.OaiSharpThresholdMonotone.Helpers.RussoMargulis
public import Papers.OaiSharpThresholdMonotone.Helpers.SupportDegree
public import Papers.OaiSharpThresholdMonotone.Main
public import Papers.OaiSharpThresholdMonotone.TThreshold
public import Papers.OaiSharpThresholdMonotone.TVariance

/-! # Run barrel (auto-generated)

Aggregates every module of this paper run so the whole run is ONE buildable target
(`lake build <this module>`). Paper modules are not reachable from the library barrels, so
the default lake target skips them and reports green on stale oleans. Rewritten from the
run's module set on every F-stage entry — do not hand-edit. -/

public section
