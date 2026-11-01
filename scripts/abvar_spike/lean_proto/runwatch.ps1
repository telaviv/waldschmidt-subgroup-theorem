param([string]$File, [int]$MaxGB = 6, [int]$MaxSec = 3000)
$dir = Split-Path -Parent $MyInvocation.MyCommand.Path
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
$log = Join-Path $dir ("log_" + [IO.Path]::GetFileNameWithoutExtension($File) + ".txt")
$sw = [Diagnostics.Stopwatch]::StartNew()
$p = Start-Process -FilePath "lake" -ArgumentList @("env", "lean", $File) -WorkingDirectory $dir -NoNewWindow -PassThru -RedirectStandardOutput $log -RedirectStandardError ($log + ".err")
$peak = 0
while (-not $p.HasExited) {
  Start-Sleep -Milliseconds 500
  $leans = Get-CimInstance Win32_Process -Filter "Name='lean.exe'" | Where-Object { $_.CommandLine -like "*$([IO.Path]::GetFileName($File))*" }
  foreach ($l in $leans) {
    $ws = $l.WorkingSetSize / 1GB
    if ($ws -gt $peak) { $peak = $ws }
    if ($ws -gt $MaxGB -or $sw.Elapsed.TotalSeconds -gt $MaxSec) {
      Stop-Process -Id $l.ProcessId -Force
      "KILLED at {0:N1}s, ws {1:N2} GB" -f $sw.Elapsed.TotalSeconds, $ws | Out-File -Append $log
    }
  }
}
"EXIT {0} elapsed {1:N1}s peakGB {2:N2}" -f $p.ExitCode, $sw.Elapsed.TotalSeconds, $peak | Out-File -Append $log
Get-Content $log
Get-Content ($log + ".err")
