param(
    [Parameter(Mandatory=$true)]
    [string]$ProjectName
)

# 1. 設定路徑
$template = "C:\Users\user\digital_tools\Lean\mathlib-template"
$target = "C:\Users\user\Desktop\digital_tools\Lean\$ProjectName"

# 2. 檢查目標資料夾是否已存在
if (Test-Path $target) {
    Write-Host "❌ 目標資料夾已存在：$target" -ForegroundColor Red
    Write-Host "請換一個專案名稱，或先手動刪除該資料夾。" -ForegroundColor Yellow
    exit
}

# 3. 複製模板
Write-Host "📦 正在複製模板..." -ForegroundColor Cyan
Copy-Item -Path $template -Destination $target -Recurse

# 4. 重新命名主 .lean 檔案
Rename-Item -Path "$target\Template.lean" -NewName "$ProjectName.lean"

# 5. 替換 lakefile.toml 內容
Write-Host "📝 正在修改 lakefile.toml..." -ForegroundColor Cyan
$tomlPath = "$target\lakefile.toml"
$content = Get-Content -Path $tomlPath -Raw
$content = $content -replace 'template', $ProjectName -replace 'Template', $ProjectName
Set-Content -Path $tomlPath -Value $content -Encoding UTF8

# 6. 進入新專案並建置
Write-Host "🔨 正在執行 lake update 和 lake build..." -ForegroundColor Cyan
Set-Location $target
lake update
lake build

Write-Host "✅ 專案 $ProjectName 建立完成！" -ForegroundColor Green
Write-Host "你可以用 VS Code 打開：$target" -ForegroundColor Green