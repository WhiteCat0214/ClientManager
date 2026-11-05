// ============================================================================
//  Mabinogi Client Manager  (ClientManager.exe)
//  瑪奇 Client.exe 的通知區域管理工具：無邊框 / 鎖定視窗、CPU 限制 (BES 風格)、優先權 / 親和性。
// ============================================================================
#define WIN32_LEAN_AND_MEAN
#define NOMINMAX
#include <windows.h>
#include <tlhelp32.h>
#include <shellapi.h>
#include <timeapi.h>
#include <string>
#include <vector>
#include <map>
#include <thread>
#include <atomic>
#include <set>
#include <mutex>
#include <algorithm>
#include <cstring>
#include <intrin.h>
#include <cstdlib>
#include <cstdio>
#include <pdh.h>
#include <pdhmsg.h>
#include <psapi.h>
#include <evntrace.h>
#include <evntcons.h>
#include <dxgi.h>
#include <winsock2.h>
#include <ws2tcpip.h>
#include <iphlpapi.h>
#include <tcpestats.h>
#include <commctrl.h>
#include "version.h"

#pragma comment(lib, "user32.lib")
#pragma comment(lib, "gdi32.lib")
#pragma comment(lib, "shell32.lib")
#pragma comment(lib, "advapi32.lib")
#pragma comment(lib, "winmm.lib")
#pragma comment(lib, "pdh.lib")
#pragma comment(lib, "psapi.lib")
#pragma comment(lib, "dxgi.lib")
#pragma comment(lib, "iphlpapi.lib")
#pragma comment(lib, "comctl32.lib")
#pragma comment(lib, "ws2_32.lib")

#ifndef CREATE_WAITABLE_TIMER_HIGH_RESOLUTION
#define CREATE_WAITABLE_TIMER_HIGH_RESOLUTION 0x00000002
#endif

#define WM_TRAYICON    (WM_APP + 1)
#define WM_UI_THROTTLE (WM_APP + 2)
#define WM_UI_OVERLAY  (WM_APP + 4)   // 取樣執行緒通知 UI 重繪監控視窗
#define WM_UI_REAPPLY  (WM_APP + 3)   // 限制解除後，請 UI 執行緒再套用一次優先權 / 親和性設定

enum {
    ID_TOGGLE = 1001, ID_RESET, ID_LOCK,
    ID_CPU_ENABLE, ID_CPU_ALW, ID_CPU_MIN, ID_CPU_BG,
    ID_ECO,
    ID_RESTART_CLIENT, ID_RESTART_LAUNCHER, ID_TERM, ID_EXIT, ID_ABOUT,
    ID_RATIO_BASE = 1100,
    ID_PRIO_CPU_BASE = 1200,   // + 等級 1..6
    ID_GPU_BASE = 1240,        // + 等級 1..6
    ID_IO_BASE = 1260,         // + 等級 1..4
    ID_SHOWTIP = 1270,
    ID_AFF_ALL = 1290, ID_AFF_P, ID_AFF_PNOHT, ID_AFF_E,
    ID_AFFCORE_BASE = 1300,    // + 邏輯核心編號 0..63
    ID_DBL_BASE = 1450,        // + 連點兩下圖示的動作 0..2
    ID_LANG_BASE = 1400,       // + 語言 0..4 (自動 / 繁中 / 簡中 / 英文 / 日文)
    ID_OV_ENABLE = 1500,       // 效能監控：啟用 / 設定視窗 / 鎖定位置
    ID_OV_SETTINGS,
    ID_OV_LOCK,
    ID_OV_LAST = 1599
};

static const int kRatios[] = { 30, 50, 70, 80, 90, 95, 98 };
static const int kRatioCount = (int)(sizeof(kRatios) / sizeof(kRatios[0]));

// ---------------------------------------------------------------------------
//  Native 函式指標
// ---------------------------------------------------------------------------
typedef LONG NtStatus;
typedef NtStatus (NTAPI* pfnNtProc)(HANDLE);
typedef NtStatus (NTAPI* pfnNtQueryInformationProcess)(HANDLE, ULONG, PVOID, ULONG, PULONG);
typedef BOOL (WINAPI* pfnSetProcessInformation)(HANDLE, int, LPVOID, DWORD);
typedef NtStatus (NTAPI* pfnNtSetInformationProcess)(HANDLE, ULONG, PVOID, ULONG);
typedef LONG (WINAPI* pfnD3dkmtSetPriority)(HANDLE, int);
typedef LONG (WINAPI* pfnD3dkmtGetPriority)(HANDLE, int*);
typedef BOOL (WINAPI* pfnSetProcessDpiAwarenessContext)(HANDLE);

struct UnicodeStr { USHORT Length; USHORT MaximumLength; PWSTR Buffer; };
struct PowerThrottleState { ULONG Version; ULONG ControlMask; ULONG StateMask; };

static pfnNtProc g_NtSuspend = NULL;
static pfnNtProc g_NtResume = NULL;
static pfnNtQueryInformationProcess g_NtQuery = NULL;
static pfnSetProcessInformation g_SetProcInfo = NULL;
static pfnNtSetInformationProcess g_NtSetInfo = NULL;
static pfnD3dkmtSetPriority g_D3dkmtSetPrio = NULL;
static pfnD3dkmtGetPriority g_D3dkmtGetPrio = NULL;

// ---------------------------------------------------------------------------
//  全域狀態
// ---------------------------------------------------------------------------
static HINSTANCE g_hInst = NULL;
static HWND g_hWnd = NULL;
static NOTIFYICONDATAW g_nid;
static HICON g_iconNormal = NULL;
static HICON g_iconBlue = NULL;
static bool g_iconNormalOwned = false;
static UINT g_wmTaskbarCreated = 0;
static HANDLE g_mutex = NULL;
static HWINEVENTHOOK g_hook1 = NULL;
static HWINEVENTHOOK g_hook2 = NULL;
static HWINEVENTHOOK g_hook3 = NULL;
static HWINEVENTHOOK g_hook4 = NULL;

static std::atomic<bool> g_cpuEnabled(false);  // CPU 限制總開關
static std::atomic<int>  g_mode(2);     // 生效條件: 1=永遠 2=最小化 (預設) 3=最小化或背景
// 以下四項「0」代表尚未設定：第一次偵測到遊戲執行時會讀取遊戲目前的值並存進設定檔，之後以設定檔的值為準
static std::atomic<int>  g_cfgCpuPrio(0);   // 1..6 = 低(Idle)/低於標準/標準/高於標準/高/即時
static std::atomic<unsigned long long> g_cfgAffMask(0);   // CPU 親和性遮罩 (bit N = 邏輯核心 N)
static std::atomic<int>  g_cfgGpuPrio(0);   // 1..6，同 CPU 優先權等級
static std::atomic<int>  g_cfgIoPrio(0);    // 1=極低 2=低 3=正常 4=高
static DWORD_PTR g_maskAll = 0, g_maskP = 0, g_maskPnoHT = 0, g_maskE = 0;   // 系統核心遮罩 / 大核 / 大核不含超執行緒 / 小核
static bool g_hybrid = false;           // 是否為大小核混合架構
static bool g_isIntel = true;           // CPU 廠牌是否為 Intel (決定顯示 Hyper-Threading 還是 SMT)
static int g_coreCount = 0;             // 邏輯核心數 (編號 0 .. N-1)
static int g_coreType[64];              // 每個邏輯核心的類型：0=未知 1=大核 2=大核超執行緒 3=小核 4=小核超執行緒 5=實體核心 6=超執行緒
static std::wstring g_topoSig;          // 目前電腦的 CPU 核心配置簽章 (設定檔換到不同 CPU 時用來判斷)
static bool g_affReset = false;         // 啟動時發現核心配置與設定檔不同，已重設親和性
static std::mutex g_loweredMtx;
static std::set<DWORD> g_lowered;       // 目前因「限制時降低優先權」而被降到低優先權的 Client 行程
struct BaseTrack { ULONGLONG since; ULONGLONG next; };
static std::map<DWORD, BaseTrack> g_base;        // 已偵測到的 Client 行程 -> 偵測時間 / 下次確認優先權與親和性的時間 (只在 UI 執行緒使用)
static std::map<HWND, POINT> g_lockPos;          // 鎖定位置時，各遊戲視窗被鎖定的左上角座標 (只在 UI 執行緒使用)
static std::atomic<DWORD> g_prioErr(0);          // 最近一次設定 CPU 優先權失敗的錯誤碼 (0 = 成功)
static bool g_throttleOn = false;                // 通知區域提示用：CPU 限制目前是否作動
static bool g_showTip = true;                    // 是否在工具提示顯示遊戲目前的優先權 / 親和性
static std::atomic<int> g_langSetting(0);        // 語言設定 (UL_*，0 = 自動)
static std::atomic<int> g_lang(1);               // 實際使用的語言 (1..4)

// ---- 效能監控 (疊加視窗) 設定與共用狀態 ----
static std::atomic<bool> g_ovEnabled(false);
static std::atomic<bool> g_ovCpu(true), g_ovCpuPct(true), g_ovCpuGhz(false);
static std::atomic<bool> g_ovRam(true), g_ovRamPct(true), g_ovRamMb(false);
static std::atomic<bool> g_ovGpu(true);
static std::atomic<bool> g_ovVram(true), g_ovVramPct(true), g_ovVramMb(false);
static std::atomic<bool> g_ovFps(true);
static std::atomic<int> g_ovLayout(0);              // 0 = 直列 (每行一項)，1 = 橫列
static std::atomic<bool> g_ovFgOnly(false);         // 只在遊戲前景時顯示 (開啟監控設定視窗期間不受影響)
static std::atomic<bool> g_ovLocked(false);         // 鎖定位置 (滑鼠穿透)
static std::atomic<bool> g_ovLockNoBg(true);        // 鎖定時無背景
static std::atomic<int> g_ovIntervalMs(1000);
static std::atomic<int> g_ovFontSize(14);           // pt
static std::atomic<int> g_ovOpacity(100);           // 整體不透明度 (%)
static std::atomic<unsigned> g_ovTextColor(0xFFFFFF);
static std::atomic<unsigned> g_ovOutlineColor(0x000000);
static std::atomic<unsigned> g_ovBgColor(0x1E1E1E);
static int g_ovX = 20, g_ovY = 20;                  // 相對所在螢幕左上角的偏移 (像素)
static std::wstring g_ovMonitor;                    // 所在螢幕的裝置名稱 (空白 = 主螢幕)
static bool g_ovDebug = false;
static std::atomic<DWORD> g_gamePid(0);             // 目前偵測到的 (第一個) Client.exe
static std::atomic<DWORD> g_fpsPid(0);
static HWND g_gameHwnd = NULL;
static HWND g_ovHwnd = NULL;
static HANDLE g_monWake = NULL;
static bool g_monDlgOpen = false;                   // 監控設定視窗是否開啟中 (開啟時固定顯示監控畫面做預覽)
static HWND g_monDlgHwnd = NULL;
static void UpdateOverlayVisibility();
static std::atomic<bool> g_ovLatency(true);         // 顯示網路延遲
static std::atomic<int> g_ovCpuMethod(0);           // CPU 使用率算法：0 = PDH 效能計數器 (預設)，1 = CPU 週期數，2 = 行程 CPU 時間
static std::atomic<int> g_ovLatMethod(0);           // Latency 取樣方式：0 = 最近一次樣本值 (預設)，1 = 平滑往返時間
static std::atomic<int> g_dblAction(0);             // 連點兩下圖示的動作：0 = 切換無邊框 / 還原，1 = 啟用 / 關閉 CPU 限制，2 = 啟用 / 關閉監控
static int g_regrayLeft = 0;                        // 「移動」變灰的連續補強次數
static bool g_noGameDlgOpen = false;
static std::wstring g_ovSeparator;                  // 橫式的分隔文字 (空白 = 只用一個空格分隔)
static std::vector<int> g_ovOrder = { 0, 1, 2, 3, 4, 5 };   // 顯示項目的順序 (OvItem：CPU / RAM / GPU / VRAM / FPS / Latency)
static void UpdateGameHook();
static void ShowNoGameDialog();
static std::atomic<ULONGLONG> g_fastUntil(0);    // 在此時間 (GetTickCount64) 之前使用密集偵測 (重啟遊戲後)
static std::atomic<bool> g_forceRefresh(false);  // 要求 CPU 限制引擎立刻重新掃描 Client 行程
static std::atomic<int> g_limitPause(0);         // >0 時暫停 CPU 限制 (調整視窗期間)
static std::atomic<bool> g_limitActive(false);   // CPU 限制目前是否正在作動
static std::atomic<int>  g_ratio(95);   // 暫停比例 (%)
static std::atomic<bool> g_eco(true);   // 限制時同時降低優先權 + EcoQoS (預設啟用)
static std::atomic<bool> g_run(true);
static std::atomic<bool> g_restarting(false);
static bool g_borderless = false;       // 只在 UI 執行緒讀寫
static bool g_locked = false;

static HANDLE g_wake = NULL;            // 喚醒引擎 (前景改變、設定改變、結束)
static HANDLE g_pauseAck = NULL;        // 引擎確認已解除暫停 (手動重設事件)
static HANDLE g_timer = NULL;           // 高解析度計時器
static bool g_hiRes = false;            // 是否取得高解析度計時器 (有的話就不需要 timeBeginPeriod)
static bool g_periodOn = false;         // 引擎執行緒專用：目前是否已提高系統計時器精度
static UINT g_syncInterval = 250;       // 視窗偵測計時器間隔：忙碌時 250ms、閒置時 1000ms
static const UINT kFastMs = 250;
static const UINT kIdleMs = 1000;
static double g_qpcFreq = 1.0;
static std::thread g_engine;

static std::wstring g_iniPath;
static std::wstring g_cachedClientPath;   // 最後一次偵測到的 Client.exe 路徑 (同步存入 ClientManager.ini)
static std::wstring g_cachedArgs;         // 最後一次偵測到的啟動參數 (同步存入 ClientManager.ini)
static DWORD g_cachedPid = 0;
static std::mutex g_pathMtx;

static std::wstring GetCachedPath() {
    std::lock_guard<std::mutex> lk(g_pathMtx);
    return g_cachedClientPath;
}

static void SetCachedPath(const std::wstring& p) {
    std::lock_guard<std::mutex> lk(g_pathMtx);
    g_cachedClientPath = p;
}

static std::wstring GetCachedArgs() {
    std::lock_guard<std::mutex> lk(g_pathMtx);
    return g_cachedArgs;
}

// ---------------------------------------------------------------------------
//  小工具
// ---------------------------------------------------------------------------
static std::wstring ExeDir() {
    wchar_t p[MAX_PATH];
    DWORD n = GetModuleFileNameW(NULL, p, MAX_PATH);
    std::wstring s(p, n);
    size_t k = s.find_last_of(L"\\/");
    return (k == std::wstring::npos) ? L"" : s.substr(0, k);
}

static std::wstring DirOf(const std::wstring& path) {
    size_t k = path.find_last_of(L"\\/");
    return (k == std::wstring::npos) ? L"" : path.substr(0, k);
}

static bool FileExists(const std::wstring& p) {
    return GetFileAttributesW(p.c_str()) != INVALID_FILE_ATTRIBUTES;
}

// ---------------------------------------------------------------------------
//  多語系：繁體中文 / 簡體中文 / 英文 / 日文
// ---------------------------------------------------------------------------
enum UiLang { UL_AUTO = 0, UL_ZHTW = 1, UL_ZHCN = 2, UL_EN = 3, UL_JA = 4 };

enum StrId {
    S_NO_GAME,
    S_NO_GAME_PATH,
    S_NO_LAUNCHER,
    S_RESTART_FAIL,
    S_NEED_ONE_CORE,
    S_ALREADY_RUNNING,
    S_AFF_RESET,
    S_TIP_LIMITING,
    S_TIP_NOGAME,
    S_TIP_HEADER,
    S_TIP_CPU,
    S_TIP_GPU,
    S_TIP_IO,
    S_TIP_CORES,
    S_PRIO_1,
    S_PRIO_2,
    S_PRIO_3,
    S_PRIO_4,
    S_PRIO_5,
    S_PRIO_6,
    S_IO_1,
    S_IO_2,
    S_IO_3,
    S_IO_4,
    S_M_TOGGLE,
    S_M_LOCK,
    S_M_RESET,
    S_M_GAMEPRIO,
    S_M_CPUPRIO,
    S_M_CPUAFF,
    S_M_GPUPRIO,
    S_M_TIPSHOW,
    S_M_IOPRIO,
    S_AFF_ALL,
    S_AFF_P,
    S_AFF_PNOHT,
    S_AFF_NOHT,
    S_AFF_E,
    S_CORE_ITEM,
    S_CORE_P,
    S_CORE_P_HT,
    S_CORE_E,
    S_CORE_E_HT,
    S_CORE_PHYS,
    S_CORE_HT,
    S_SMT_INTEL,
    S_SMT_OTHER,
    S_M_LIMIT,
    S_M_ENABLE,
    S_M_ECO,
    S_M_COND,
    S_C_ALWAYS,
    S_C_MIN,
    S_C_BG,
    S_M_RATIO,
    S_M_RESTARTMENU,
    S_M_RESTART_CLIENT,
    S_M_RESTART_LAUNCHER,
    S_M_TERM,
    S_M_LANG,
    S_L_AUTO,
    S_OV_LIMITING,
    S_M_MON,
    S_MON_ENABLE,
    S_MON_ITEMS,
    S_MON_PCT,
    S_MON_ACTUAL_GHZ,
    S_MON_ACTUAL_MB,
    S_MON_LAYOUT,
    S_MON_VERT,
    S_MON_HORZ,
    S_MON_LOCK,
    S_MON_INTERVAL,
    S_MON_STYLE,
    S_MON_FONTSIZE,
    S_MON_OPACITY,
    S_MON_LOCKNOBG,
    S_MON_RESETPOS,
    S_DLG_COLOR_BAD,
    S_DLG_OK,
    S_DLG_CANCEL,
    S_MON_SETTINGS,
    S_DLG_MON_TITLE,
    S_DLG_APPLY,
    S_LBL_TEXTCOLOR,
    S_LBL_OUTLINECOLOR,
    S_LBL_BGCOLOR,
    S_MON_FGONLY_DLG,
    S_MON_EVERY_05,
    S_MON_EVERY_1,
    S_MON_EVERY_2,
    S_M_DBLCLICK,
    S_DBL_CPU,
    S_DBL_MON,
    S_DLG_RESTART_CLIENT,
    S_DLG_RESTART_LAUNCHER,
    S_DLG_CLOSE,
    S_MON_DISPLAY,
    S_MON_SEPARATOR,
    S_MON_ORDER,
    S_MON_METHOD,
    S_METHOD_CYC,
    S_METHOD_TIME,
    S_MON_DEBUG,
    S_DLG_COPY,
    S_MON_LATMETHOD,
    S_LAT_SAMPLE,
    S_LAT_SMOOTH,
    S_METHOD_EST,
    S_M_ABOUT,
    S_ABOUT_TITLE,
    S_ABOUT_GROUP,
    S_ABOUT_TEXT,
    S_DLG_STOP_UPDATE,
    S_DLG_AUTO_UPDATE,
    S_ABOUT_VERSION,
    S_M_EXIT,
    S__COUNT
};

static const wchar_t* const kStr[S__COUNT][4] = {
    { L"找不到執行中的遊戲 (Client.exe)！\n需先手動執行一次遊戲，才能使用此功能。", L"找不到正在运行的游戏 (Client.exe)！\n需要先手动运行一次游戏，才能使用此功能。", L"No running game (Client.exe) found!\nStart the game manually at least once before using this feature.", L"実行中のゲーム (Client.exe) が見つかりません。\nこの機能を使うには、先に一度ゲームを手動で起動してください。" },   // NO_GAME
    { L"找不到執行中的遊戲 (Client.exe)！\n需先手動執行一次遊戲，工具才能記住遊戲路徑。", L"找不到正在运行的游戏 (Client.exe)！\n需要先手动运行一次游戏，工具才能记住游戏路径。", L"No running game (Client.exe) found!\nStart the game manually once so the tool can remember its path.", L"実行中のゲーム (Client.exe) が見つかりません。\n一度ゲームを手動で起動して、パスを記憶させてください。" },   // NO_GAME_PATH
    { L"找不到同目錄下的遊戲啟動器 (Mabinogi.exe)！\n需先手動執行遊戲一次，或確認遊戲資料夾是否完整。", L"找不到同目录下的游戏启动器 (Mabinogi.exe)！\n需要先手动运行一次游戏，或确认游戏文件夹是否完整。", L"Game launcher (Mabinogi.exe) not found in the same folder!\nStart the game manually once, or check that the game folder is intact.", L"同じフォルダーにゲームランチャー (Mabinogi.exe) が見つかりません。\n一度ゲームを手動で起動するか、ゲームフォルダーを確認してください。" },   // NO_LAUNCHER
    { L"重啟遊戲失敗 (錯誤碼 %lu)", L"重启游戏失败 (错误码 %lu)", L"Failed to restart the game (error code %lu)", L"ゲームの再起動に失敗しました (エラーコード %lu)" },   // RESTART_FAIL
    { L"至少需要選擇一個核心！", L"至少需要选择一个核心！", L"At least one core must be selected!", L"少なくとも 1 つのコアを選択してください。" },   // NEED_ONE_CORE
    { L"Mabinogi Client Manager 已經在背景執行中！", L"Mabinogi Client Manager 已经在后台运行！", L"Mabinogi Client Manager is already running in the background!", L"Mabinogi Client Manager は既にバックグラウンドで実行中です。" },   // ALREADY_RUNNING
    { L"偵測到 CPU 核心配置與設定檔記錄的不同 (可能更換了電腦或 CPU)，\n已重設 CPU 親和性，將在遊戲啟動時重新讀取遊戲目前的設定。", L"检测到 CPU 核心配置与配置文件记录的不同 (可能更换了电脑或 CPU)，\n已重置 CPU 亲和性，将在游戏启动时重新读取游戏当前的设置。", L"The CPU core layout differs from the one saved in the settings file (the PC or CPU may have changed).\nCPU affinity has been reset and will be re-read from the game the next time it starts.", L"CPU のコア構成が設定ファイルの記録と異なります (PC または CPU が変更された可能性があります)。\nCPU アフィニティをリセットしました。次回ゲーム起動時に現在の設定を読み込みます。" },   // AFF_RESET
    { L" (限制中)", L" (限制中)", L" (Limiting)", L" (制限中)" },   // TIP_LIMITING
    { L"遊戲未執行", L"游戏未运行", L"Game not running", L"ゲーム未実行" },   // TIP_NOGAME
    { L"目前的遊戲優先權 / 親和性", L"当前的游戏优先级 / 亲和性", L"Current game priority / affinity", L"現在のゲームの優先度 / アフィニティ" },   // TIP_HEADER
    { L"CPU: %s", L"CPU: %s", L"CPU: %s", L"CPU: %s" },   // TIP_CPU
    { L"GPU: %s", L"GPU: %s", L"GPU: %s", L"GPU: %s" },   // TIP_GPU
    { L"I/O: %s", L"I/O: %s", L"I/O: %s", L"I/O: %s" },   // TIP_IO
    { L"核心: %s", L"核心: %s", L"Cores: %s", L"コア: %s" },   // TIP_CORES
    { L"低 (Idle)", L"低 (Idle)", L"Idle", L"低 (Idle)" },   // PRIO_1
    { L"低於標準", L"低于标准", L"Below normal", L"通常以下" },   // PRIO_2
    { L"標準", L"标准", L"Normal", L"通常" },   // PRIO_3
    { L"高於標準", L"高于标准", L"Above normal", L"通常以上" },   // PRIO_4
    { L"高", L"高", L"High", L"高" },   // PRIO_5
    { L"即時 (Realtime)", L"实时 (Realtime)", L"Realtime", L"リアルタイム (Realtime)" },   // PRIO_6
    { L"極低", L"极低", L"Very low", L"非常に低い" },   // IO_1
    { L"低", L"低", L"Low", L"低" },   // IO_2
    { L"正常", L"正常", L"Normal", L"通常" },   // IO_3
    { L"高", L"高", L"High", L"高" },   // IO_4
    { L"切換無邊框 / 還原", L"切换无边框 / 还原", L"Toggle borderless / restore", L"ボーダーレス切替 / 元に戻す" },   // M_TOGGLE
    { L"鎖定視窗大小及位置", L"锁定窗口大小及位置", L"Lock window size and position", L"ウィンドウのサイズと位置を固定" },   // M_LOCK
    { L"重置視窗大小和位置", L"重置窗口大小和位置", L"Reset window size and position", L"ウィンドウのサイズと位置をリセット" },   // M_RESET
    { L"遊戲優先權 / 親和性", L"游戏优先级 / 亲和性", L"Game priority / affinity", L"ゲームの優先度 / アフィニティ" },   // M_GAMEPRIO
    { L"CPU優先權", L"CPU优先级", L"CPU priority", L"CPU 優先度" },   // M_CPUPRIO
    { L"CPU親和性", L"CPU亲和性", L"CPU affinity", L"CPU アフィニティ" },   // M_CPUAFF
    { L"GPU優先權", L"GPU优先级", L"GPU priority", L"GPU 優先度" },   // M_GPUPRIO
    { L"於工具提示顯示目前狀態", L"在工具提示中显示当前状态", L"Show current status in tooltip", L"ツールチップに現在の状態を表示" },   // M_TIPSHOW
    { L"I/O優先權", L"I/O优先级", L"I/O priority", L"I/O 優先度" },   // M_IOPRIO
    { L"全選", L"全选", L"Select all", L"すべて選択" },   // AFF_ALL
    { L"僅大核 (P-core)", L"仅大核 (P-core)", L"P-cores only", L"P コアのみ" },   // AFF_P
    { L"僅大核 (P-core) 不含%s", L"仅大核 (P-core) 不含%s", L"P-cores only (no %s)", L"P コアのみ (%s なし)" },   // AFF_PNOHT
    { L"僅實體核心 (不含%s)", L"仅物理核心 (不含%s)", L"Physical cores only (no %s)", L"物理コアのみ (%s なし)" },   // AFF_NOHT
    { L"僅小核 (E-core)", L"仅小核 (E-core)", L"E-cores only", L"E コアのみ" },   // AFF_E
    { L"核心 %d %s", L"核心 %d %s", L"Core %d %s", L"コア %d %s" },   // CORE_ITEM
    { L"(大核 P-core)", L"(大核 P-core)", L"(P-core)", L"(P コア)" },   // CORE_P
    { L"(大核 P-core) %s", L"(大核 P-core) %s", L"(P-core) %s", L"(P コア) %s" },   // CORE_P_HT
    { L"(小核 E-core)", L"(小核 E-core)", L"(E-core)", L"(E コア)" },   // CORE_E
    { L"(小核 E-core) %s", L"(小核 E-core) %s", L"(E-core) %s", L"(E コア) %s" },   // CORE_E_HT
    { L"(實體核心)", L"(物理核心)", L"(Physical core)", L"(物理コア)" },   // CORE_PHYS
    { L"(%s)", L"(%s)", L"(%s)", L"(%s)" },   // CORE_HT
    { L"超執行緒", L"超线程", L"Hyper-Threading", L"ハイパースレッディング" },   // SMT_INTEL
    { L"超執行緒", L"超线程", L"SMT", L"SMT" },   // SMT_OTHER
    { L"限制CPU使用率", L"限制CPU使用率", L"Limit CPU usage", L"CPU 使用率を制限" },   // M_LIMIT
    { L"啟用CPU限制", L"启用CPU限制", L"Enable CPU limit", L"CPU 制限を有効にする" },   // M_ENABLE
    { L"限制時同時降低優先權 / 節能模式", L"限制时同时降低优先级 / 节能模式", L"Lower priority / efficiency mode while limiting", L"制限中は優先度を下げる / 省電力モード" },   // M_ECO
    { L"生效條件", L"生效条件", L"When to apply", L"適用条件" },   // M_COND
    { L"永遠限制 CPU 使用率", L"始终限制 CPU 使用率", L"Always limit CPU usage", L"常に CPU 使用率を制限" },   // C_ALWAYS
    { L"僅在視窗最小化時生效", L"仅在窗口最小化时生效", L"Only when the window is minimized", L"ウィンドウ最小化時のみ" },   // C_MIN
    { L"僅在視窗最小化或於背景執行時生效", L"仅在窗口最小化或在后台运行时生效", L"Only when minimized or in the background", L"最小化またはバックグラウンド時のみ" },   // C_BG
    { L"限制比例", L"限制比例", L"Limit ratio", L"制限割合" },   // M_RATIO
    { L"強制重啟 / 結束遊戲", L"强制重启 / 结束游戏", L"Force restart / quit game", L"ゲームの強制再起動 / 終了" },   // M_RESTARTMENU
    { L"重啟遊戲 (Client.exe)", L"重启游戏 (Client.exe)", L"Restart game (Client.exe)", L"ゲームを再起動 (Client.exe)" },   // M_RESTART_CLIENT
    { L"重啟遊戲 (Mabinogi.exe)", L"重启游戏 (Mabinogi.exe)", L"Restart game (Mabinogi.exe)", L"ゲームを再起動 (Mabinogi.exe)" },   // M_RESTART_LAUNCHER
    { L"強制結束遊戲", L"强制结束游戏", L"Force quit game", L"ゲームを強制終了" },   // M_TERM
    { L"語言", L"语言", L"Language", L"言語" },   // M_LANG
    { L"自動選擇", L"自动选择", L"Auto", L"自動選択" },   // L_AUTO
    { L"(限制中)", L"(限制中)", L"(Limited)", L"(制限中)" },   // OV_LIMITING
    { L"效能監控", L"性能监控", L"Performance monitor", L"パフォーマンスモニター" },   // M_MON
    { L"啟用監控", L"启用监控", L"Enable monitor", L"モニターを有効にする" },   // MON_ENABLE
    { L"顯示項目", L"显示项目", L"Items", L"表示項目" },   // MON_ITEMS
    { L"比例", L"比例", L"Percentage", L"割合" },   // MON_PCT
    { L"實際值 (GHz)", L"实际值 (GHz)", L"Actual value (GHz)", L"実測値 (GHz)" },   // MON_ACTUAL_GHZ
    { L"實際值 (MB)", L"实际值 (MB)", L"Actual value (MB)", L"実測値 (MB)" },   // MON_ACTUAL_MB
    { L"排列方式", L"排列方式", L"Layout", L"レイアウト" },   // MON_LAYOUT
    { L"直式 (每行一項)", L"竖式 (每行一项)", L"Vertical (one item per line)", L"縦 (1 行に 1 項目)" },   // MON_VERT
    { L"橫式 (以文字分隔)", L"横式 (以文字分隔)", L"Horizontal (separated by text)", L"横 (文字で区切る)" },   // MON_HORZ
    { L"鎖定位置 (滑鼠穿透)", L"锁定位置 (鼠标穿透)", L"Lock position (click-through)", L"位置を固定 (クリックを透過)" },   // MON_LOCK
    { L"更新頻率", L"更新频率", L"Update interval", L"更新間隔" },   // MON_INTERVAL
    { L"外觀", L"外观", L"Appearance", L"外観" },   // MON_STYLE
    { L"字體大小", L"字体大小", L"Font size", L"フォントサイズ" },   // MON_FONTSIZE
    { L"不透明度", L"不透明度", L"Opacity", L"不透明度" },   // MON_OPACITY
    { L"鎖定時無背景", L"锁定时无背景", L"No background when locked", L"固定時は背景なし" },   // MON_LOCKNOBG
    { L"重置位置", L"重置位置", L"Reset position", L"位置をリセット" },   // MON_RESETPOS
    { L"色碼格式不正確，請輸入 6 位數的 HEX (0-9、A-F)。", L"色码格式不正确，请输入 6 位 HEX (0-9、A-F)。", L"Invalid color code. Enter 6 hex digits (0-9, A-F).", L"カラーコードの形式が正しくありません。16 進数 6 桁 (0-9, A-F) で入力してください。" },   // DLG_COLOR_BAD
    { L"確定", L"确定", L"OK", L"OK" },   // DLG_OK
    { L"取消", L"取消", L"Cancel", L"キャンセル" },   // DLG_CANCEL
    { L"監控設定...", L"监控设置...", L"Monitor settings...", L"モニター設定..." },   // MON_SETTINGS
    { L"監控設定", L"监控设置", L"Monitor settings", L"モニター設定" },   // DLG_MON_TITLE
    { L"套用", L"应用", L"Apply", L"適用" },   // DLG_APPLY
    { L"字體顏色", L"字体颜色", L"Text color", L"文字の色" },   // LBL_TEXTCOLOR
    { L"文字外框顏色", L"文字外框颜色", L"Text outline color", L"文字の縁取りの色" },   // LBL_OUTLINECOLOR
    { L"背景顏色", L"背景颜色", L"Background color", L"背景色" },   // LBL_BGCOLOR
    { L"只在遊戲前景時顯示 (僅在設定視窗關閉後生效)", L"仅在游戏前台时显示 (仅在设置窗口关闭后生效)", L"Show only when the game is in the foreground (takes effect after this window is closed)", L"ゲームが前面のときのみ表示 (この画面を閉じた後に有効)" },   // MON_FGONLY_DLG
    { L"每 0.5 秒", L"每 0.5 秒", L"Every 0.5 s", L"0.5 秒ごと" },   // MON_EVERY_05
    { L"每 1 秒", L"每 1 秒", L"Every 1 s", L"1 秒ごと" },   // MON_EVERY_1
    { L"每 2 秒", L"每 2 秒", L"Every 2 s", L"2 秒ごと" },   // MON_EVERY_2
    { L"連點兩下圖示的動作", L"双击图标的动作", L"Double-click action", L"ダブルクリックの動作" },   // M_DBLCLICK
    { L"啟用CPU限制 / 關閉CPU限制", L"启用CPU限制 / 关闭CPU限制", L"Enable / disable CPU limit", L"CPU 制限の有効 / 無効を切り替え" },   // DBL_CPU
    { L"啟用監控 / 關閉監控", L"启用监控 / 关闭监控", L"Enable / disable monitor", L"モニターの有効 / 無効を切り替え" },   // DBL_MON
    { L"重啟 Client.exe", L"重启 Client.exe", L"Restart Client.exe", L"Client.exe を再起動" },   // DLG_RESTART_CLIENT
    { L"重啟 Mabinogi.exe", L"重启 Mabinogi.exe", L"Restart Mabinogi.exe", L"Mabinogi.exe を再起動" },   // DLG_RESTART_LAUNCHER
    { L"關閉", L"关闭", L"Close", L"閉じる" },   // DLG_CLOSE
    { L"顯示設定", L"显示设置", L"Display settings", L"表示設定" },   // MON_DISPLAY
    { L"分隔文字", L"分隔文字", L"Separator", L"区切り文字" },   // MON_SEPARATOR
    { L"顯示順序 (拖曳排序)", L"显示顺序 (拖动排序)", L"Order (drag to sort)", L"表示順序 (ドラッグ)" },   // MON_ORDER
    { L"CPU 使用率算法", L"CPU 使用率算法", L"CPU usage method", L"CPU 使用率の算出方法" },   // MON_METHOD
    { L"週期法 (CPU 週期數)", L"周期法 (CPU 周期数)", L"Cycle count", L"サイクル数" },   // METHOD_CYC
    { L"時間法 (行程 CPU 時間)", L"时间法 (进程 CPU 时间)", L"Process CPU time", L"プロセス CPU 時間" },   // METHOD_TIME
    { L"診斷記錄", L"诊断记录", L"Diagnostic log", L"診断ログ" },   // MON_DEBUG
    { L"複製", L"复制", L"Copy", L"コピー" },   // DLG_COPY
    { L"Latency 取樣方式", L"Latency 取样方式", L"Latency sampling", L"Latency の取得方法" },   // MON_LATMETHOD
    { L"最近一次樣本值 (預設)", L"最近一次样本值 (默认)", L"Latest sample (default)", L"最新のサンプル値 (既定)" },   // LAT_SAMPLE
    { L"平滑往返時間", L"平滑往返时间", L"Smoothed round-trip time", L"平滑化した往復時間" },   // LAT_SMOOTH
    { L"估算 (行程時間 × 系統 Utility/Time)", L"估算 (进程时间 × 系统 Utility/Time)", L"Estimate (process time x system utility/time)", L"推定 (プロセス時間 × システム Utility/Time)" },   // METHOD_EST
    { L"關於...", L"关于...", L"About...", L"バージョン情報..." },   // M_ABOUT
    { L"關於", L"关于", L"About", L"バージョン情報" },   // ABOUT_TITLE
    { L"程式說明", L"程序说明", L"Description", L"プログラムの説明" },   // ABOUT_GROUP
    { L"瑪奇 (Mabinogi) Client.exe 的常駐管理工具 (顯示於通知區域)\n\n【主要功能說明】\n  ．視窗無邊框 / 鎖定大小位置 / 還原 (類似 Kisara 的偽全屏)\n  ．限制CPU使用率 (類似 BES, Battle Encoder Shirase 的CPU限制軟體)\n  ．優先權與親和性設定 (類似 Process Lasso 的程式優先權及CPU親和性的調整)\n  ．效能監控 (類似 XBOX Gamebar 的效能監控，另外加上資源監視器的網路TCP連線延遲資訊)",
      L"玛奇 (Mabinogi) Client.exe 的常驻管理工具 (显示于通知区域)\n\n【主要功能说明】\n  ．窗口无边框 / 锁定大小位置 / 还原 (类似 Kisara 的伪全屏)\n  ．限制CPU使用率 (类似 BES, Battle Encoder Shirase 的CPU限制软件)\n  ．优先级与亲和性设置 (类似 Process Lasso 的程序优先级及CPU亲和性的调整)\n  ．性能监控 (类似 XBOX Game Bar 的性能监控，另外加上资源监视器的网络TCP连接延迟信息)",
      L"A resident manager for Mabinogi's Client.exe (shown in the notification area)\n\n[Main features]\n  - Borderless window / lock size and position / restore (like Kisara's pseudo fullscreen)\n  - CPU usage limiting (like BES, Battle Encoder Shirase)\n  - Priority and affinity settings (like Process Lasso)\n  - Performance monitor (like the Xbox Game Bar, plus the TCP connection latency from Resource Monitor)",
      L"マビノギ (Mabinogi) Client.exe の常駐管理ツール (通知領域に表示)\n\n【主な機能】\n  ・ウィンドウのボーダーレス化 / サイズと位置のロック / 元に戻す (Kisara の疑似フルスクリーンに類似)\n  ・CPU 使用率の制限 (BES, Battle Encoder Shirase に類似)\n  ・優先度とアフィニティの設定 (Process Lasso に類似)\n  ・パフォーマンス モニター (Xbox Game Bar に類似、リソース モニターの TCP 接続遅延情報も追加)" },   // ABOUT_TEXT
    { L"停止更新", L"停止更新", L"Stop updating", L"更新を停止" },   // DLG_STOP_UPDATE
    { L"自動更新", L"自动更新", L"Auto update", L"自動更新" },   // DLG_AUTO_UPDATE
    { L"版本", L"版本", L"Version", L"バージョン" },   // ABOUT_VERSION
    { L"結束程式", L"退出程序", L"Exit", L"終了" },   // M_EXIT
};

static inline const wchar_t* T(int id) { return kStr[id][g_lang - 1]; }

// Intel 稱 Hyper-Threading，AMD 等其他廠牌稱 SMT
static const wchar_t* SmtName() { return T(g_isIntel ? S_SMT_INTEL : S_SMT_OTHER); }

// 取得含「超執行緒 / Hyper-Threading / SMT」用詞的字串
static std::wstring TS(int id) {
    wchar_t b[256];
    wsprintfW(b, T(id), SmtName());
    return b;
}

static void DetectCpuVendor() {
    int r[4] = { 0, 0, 0, 0 };
    __cpuid(r, 0);
    char v[13];
    memcpy(v, &r[1], 4);
    memcpy(v + 4, &r[3], 4);
    memcpy(v + 8, &r[2], 4);
    v[12] = 0;
    g_isIntel = (strcmp(v, "GenuineIntel") == 0);
}

static int DetectSystemLang() {
    LANGID id = GetUserDefaultUILanguage();
    WORD p = PRIMARYLANGID(id), sub = SUBLANGID(id);
    if (p == LANG_CHINESE) return (sub == SUBLANG_CHINESE_SIMPLIFIED || sub == SUBLANG_CHINESE_SINGAPORE) ? UL_ZHCN : UL_ZHTW;
    if (p == LANG_JAPANESE) return UL_JA;
    return UL_EN;
}

// 優先讀設定檔的語言；設定為「自動」(或沒有設定) 時依系統語系
static void ApplyLanguage() {
    int sel = g_langSetting;
    g_lang = (sel >= UL_ZHTW && sel <= UL_JA) ? sel : DetectSystemLang();
}

static const wchar_t* LangName(int l) {
    switch (l) {
    case UL_ZHTW: return L"zh-TW";
    case UL_ZHCN: return L"zh-CN";
    case UL_EN: return L"en";
    case UL_JA: return L"jp";
    }
    return L"auto";
}

static int LangFromName(const wchar_t* n) {
    if (_wcsicmp(n, L"zh-TW") == 0) return UL_ZHTW;
    if (_wcsicmp(n, L"zh-CN") == 0) return UL_ZHCN;
    if (_wcsicmp(n, L"en") == 0) return UL_EN;
    if (_wcsicmp(n, L"jp") == 0) return UL_JA;
    return UL_AUTO;
}

static std::atomic<bool> g_msgOpen(false);

// 以獨立執行緒顯示提示對話框：不會卡住通知區域選單，也不會被系統的「通知」設定擋掉
static void Notify(const std::wstring& text, UINT icon = MB_ICONWARNING) {
    if (g_msgOpen.exchange(true)) return;   // 已有提示視窗開著就不重複彈出
    std::wstring* s = new std::wstring(text);
    std::thread([s, icon]() {
        MessageBoxW(NULL, s->c_str(), L"Mabinogi Client Manager", MB_OK | icon | MB_TOPMOST | MB_SETFOREGROUND);
        delete s;
        g_msgOpen = false;
    }).detach();
}

static void WakeEngine() {
    if (g_wake) SetEvent(g_wake);
}

// 調整視窗大小期間先短暫解除 CPU 限制 (遊戲被暫停時，視窗訊息會被延遲)，完成後自動恢復
static void PauseLimit() {
    if (g_pauseAck) ResetEvent(g_pauseAck);
    g_limitPause++;
    if (g_limitActive) {
        WakeEngine();
        if (g_pauseAck) WaitForSingleObject(g_pauseAck, 400);   // 等引擎確認已解除暫停
    }
}

static void ResumeLimit() {
    g_limitPause--;
    WakeEngine();
}

struct LimitPause {
    LimitPause() { PauseLimit(); }
    ~LimitPause() { ResumeLimit(); }
};

// ---------------------------------------------------------------------------
//  設定檔 (ClientManager.ini，UTF-16)
// ---------------------------------------------------------------------------
static void EnsureUnicodeIni() {
    if (g_iniPath.empty() || FileExists(g_iniPath)) return;
    HANDLE h = CreateFileW(g_iniPath.c_str(), GENERIC_WRITE, 0, NULL, CREATE_NEW, FILE_ATTRIBUTE_NORMAL, NULL);
    if (h == INVALID_HANDLE_VALUE) return;
    const unsigned char bom[2] = { 0xFF, 0xFE };
    DWORD w = 0;
    WriteFile(h, bom, 2, &w, NULL);
    CloseHandle(h);
}

static void SaveString(const wchar_t* key, const std::wstring& v) {
    EnsureUnicodeIni();
    WritePrivateProfileStringW(L"Settings", key, v.c_str(), g_iniPath.c_str());
}

static void SaveInt(const wchar_t* key, int v) {
    wchar_t b[16];
    wsprintfW(b, L"%d", v);
    SaveString(key, b);
}

// 更新「最後一次的路徑與參數」；有變動才寫入設定檔
static void UpdateClientCache(const std::wstring& path, const std::wstring& args) {
    bool pathChanged = false;
    bool argsChanged = false;
    {
        std::lock_guard<std::mutex> lk(g_pathMtx);
        pathChanged = (g_cachedClientPath != path);
        argsChanged = (g_cachedArgs != args);
        g_cachedClientPath = path;
        g_cachedArgs = args;
    }
    if (pathChanged) SaveString(L"ClientPath", path);
    if (argsChanged) SaveString(L"ClientArgs", args);
}

static std::wstring U64ToStr(unsigned long long v) {
    if (v == 0) return L"0";
    std::wstring r;
    while (v) {
        r.insert(r.begin(), (wchar_t)(L'0' + (int)(v % 10)));
        v /= 10;
    }
    return r;
}

static unsigned long long StrToU64(const wchar_t* p) {
    unsigned long long v = 0;
    while (*p >= L'0' && *p <= L'9') {
        v = v * 10 + (unsigned long long)(*p - L'0');
        ++p;
    }
    return v;
}

// ---------------------------------------------------------------------------
//  效能監控設定 (ClientManager.ini)
// ---------------------------------------------------------------------------
static bool ParseHex6(const wchar_t* s, unsigned* out) {
    if (*s == L'#') ++s;
    unsigned v = 0;
    int n = 0;
    for (; *s; ++s, ++n) {
        wchar_t c = *s;
        unsigned d;
        if (c >= L'0' && c <= L'9') d = (unsigned)(c - L'0');
        else if (c >= L'a' && c <= L'f') d = (unsigned)(c - L'a' + 10);
        else if (c >= L'A' && c <= L'F') d = (unsigned)(c - L'A' + 10);
        else return false;
        v = v * 16 + d;
    }
    if (n != 6) return false;
    *out = v;
    return true;
}

static std::wstring Hex6(unsigned v) {
    wchar_t b[16];
    wsprintfW(b, L"%06X", v & 0xFFFFFF);
    return b;
}

// 顯示項目 (順序可調整)：0 = CPU、1 = RAM、2 = GPU、3 = VRAM、4 = FPS、5 = Latency
enum OvItem { OVI_CPU, OVI_RAM, OVI_GPU, OVI_VRAM, OVI_FPS, OVI_LAT, OVI_COUNT };
static const wchar_t* const kOvItemNames[OVI_COUNT] = { L"CPU", L"RAM", L"GPU", L"VRAM", L"FPS", L"Latency" };

static std::vector<int> ParseOvOrder(const std::wstring& s) {
    std::vector<int> out;
    bool used[OVI_COUNT] = { false, false, false, false, false, false };
    size_t pos = 0;
    while (pos <= s.size()) {
        size_t e = s.find(L',', pos);
        if (e == std::wstring::npos) e = s.size();
        std::wstring tok = s.substr(pos, e - pos);
        while (!tok.empty() && tok[0] == L' ') tok.erase(0, 1);
        while (!tok.empty() && tok[tok.size() - 1] == L' ') tok.erase(tok.size() - 1, 1);
        for (int i = 0; i < OVI_COUNT; ++i) {
            if (!used[i] && _wcsicmp(tok.c_str(), kOvItemNames[i]) == 0) {
                used[i] = true;
                out.push_back(i);
                break;
            }
        }
        pos = e + 1;
    }
    for (int i = 0; i < OVI_COUNT; ++i) if (!used[i]) out.push_back(i);   // 缺少的項目依預設順序補在後面
    return out;
}

static std::wstring JoinOvOrder(const std::vector<int>& v) {
    std::wstring s;
    for (size_t i = 0; i < v.size(); ++i) {
        if (v[i] < 0 || v[i] >= OVI_COUNT) continue;
        if (!s.empty()) s += L",";
        s += kOvItemNames[v[i]];
    }
    return s;
}

static bool IniBool(const wchar_t* key, int def) {
    return GetPrivateProfileIntW(L"Settings", key, def, g_iniPath.c_str()) != 0;
}

static int IniInt(const wchar_t* key, int def, int lo, int hi) {
    int v = (int)GetPrivateProfileIntW(L"Settings", key, def, g_iniPath.c_str());
    return std::max(lo, std::min(hi, v));
}

static unsigned IniColor(const wchar_t* key, unsigned def) {
    wchar_t b[32];
    b[0] = 0;
    GetPrivateProfileStringW(L"Settings", key, L"", b, 32, g_iniPath.c_str());
    unsigned v;
    return ParseHex6(b, &v) ? v : def;
}

static void LoadOverlaySettings() {
    g_ovEnabled = IniBool(L"OvEnabled", 0);
    g_ovCpu = IniBool(L"OvCpu", 1);
    g_ovCpuPct = IniBool(L"OvCpuPct", 1);
    g_ovCpuGhz = IniBool(L"OvCpuGhz", 0);
    g_ovRam = IniBool(L"OvRam", 1);
    g_ovRamPct = IniBool(L"OvRamPct", 1);
    g_ovRamMb = IniBool(L"OvRamMb", 0);
    g_ovGpu = IniBool(L"OvGpu", 1);
    g_ovVram = IniBool(L"OvVram", 1);
    g_ovVramPct = IniBool(L"OvVramPct", 1);
    g_ovVramMb = IniBool(L"OvVramMb", 0);
    g_ovFps = IniBool(L"OvFps", 1);
    g_ovLatency = IniBool(L"OvLatency", 1);
    g_ovCpuMethod = IniInt(L"OvCpuMethod", 0, 0, 2);
    g_ovLatMethod = IniInt(L"OvLatencyMethod", 0, 0, 1);
    {
        wchar_t sb[64], ob[128];
        sb[0] = 0;
        ob[0] = 0;
        GetPrivateProfileStringW(L"Settings", L"OvSeparator", L"", sb, 64, g_iniPath.c_str());
        GetPrivateProfileStringW(L"Settings", L"OvOrder", L"", ob, 128, g_iniPath.c_str());
        g_ovSeparator = sb;
        g_ovOrder = ParseOvOrder(ob);
    }
    g_dblAction = IniInt(L"DoubleClick", 0, 0, 2);
    g_ovLayout = IniInt(L"OvLayout", 0, 0, 1);
    g_ovFgOnly = IniBool(L"OvFgOnly", 0);
    g_ovLocked = IniBool(L"OvLocked", 0);
    g_ovLockNoBg = IniBool(L"OvLockNoBg", 1);
    g_ovIntervalMs = IniInt(L"OvInterval", 1000, 250, 5000);
    g_ovFontSize = IniInt(L"OvFontSize", 14, 8, 48);
    g_ovOpacity = IniInt(L"OvOpacity", 100, 20, 100);
    g_ovTextColor = IniColor(L"OvTextColor", 0xFFFFFF);
    g_ovOutlineColor = IniColor(L"OvOutlineColor", 0x000000);
    g_ovBgColor = IniColor(L"OvBgColor", 0x1E1E1E);
    g_ovX = IniInt(L"OvX", 20, 0, 20000);
    g_ovY = IniInt(L"OvY", 20, 0, 20000);
    wchar_t b[64];
    b[0] = 0;
    GetPrivateProfileStringW(L"Settings", L"OvMonitor", L"", b, 64, g_iniPath.c_str());
    g_ovMonitor = b;
}

static void SaveOverlaySettings() {
    SaveInt(L"OvEnabled", g_ovEnabled ? 1 : 0);
    SaveInt(L"OvCpu", g_ovCpu ? 1 : 0);
    SaveInt(L"OvCpuPct", g_ovCpuPct ? 1 : 0);
    SaveInt(L"OvCpuGhz", g_ovCpuGhz ? 1 : 0);
    SaveInt(L"OvRam", g_ovRam ? 1 : 0);
    SaveInt(L"OvRamPct", g_ovRamPct ? 1 : 0);
    SaveInt(L"OvRamMb", g_ovRamMb ? 1 : 0);
    SaveInt(L"OvGpu", g_ovGpu ? 1 : 0);
    SaveInt(L"OvVram", g_ovVram ? 1 : 0);
    SaveInt(L"OvVramPct", g_ovVramPct ? 1 : 0);
    SaveInt(L"OvVramMb", g_ovVramMb ? 1 : 0);
    SaveInt(L"OvFps", g_ovFps ? 1 : 0);
    SaveInt(L"OvLatency", g_ovLatency ? 1 : 0);
    SaveInt(L"OvCpuMethod", g_ovCpuMethod);
    SaveInt(L"OvLatencyMethod", g_ovLatMethod);
    SaveString(L"OvSeparator", g_ovSeparator);
    SaveString(L"OvOrder", JoinOvOrder(g_ovOrder));
    SaveInt(L"DoubleClick", g_dblAction);
    SaveInt(L"OvLayout", g_ovLayout);
    SaveInt(L"OvFgOnly", g_ovFgOnly ? 1 : 0);
    SaveInt(L"OvLocked", g_ovLocked ? 1 : 0);
    SaveInt(L"OvLockNoBg", g_ovLockNoBg ? 1 : 0);
    SaveInt(L"OvInterval", g_ovIntervalMs);
    SaveInt(L"OvFontSize", g_ovFontSize);
    SaveInt(L"OvOpacity", g_ovOpacity);
    SaveString(L"OvTextColor", Hex6(g_ovTextColor));
    SaveString(L"OvOutlineColor", Hex6(g_ovOutlineColor));
    SaveString(L"OvBgColor", Hex6(g_ovBgColor));
    SaveInt(L"OvX", g_ovX);
    SaveInt(L"OvY", g_ovY);
    SaveString(L"OvMonitor", g_ovMonitor);
}

static void SaveWindowState() {
    SaveInt(L"Borderless", g_borderless ? 1 : 0);
    SaveInt(L"Locked", g_locked ? 1 : 0);
}

// 啟動時把所有設定 (含預設值) 都寫進設定檔，讓檔案一開始就是完整的
static void SaveAllSettings() {
    SaveInt(L"CpuEnabled", g_cpuEnabled ? 1 : 0);
    SaveInt(L"CpuMode", g_mode);
    SaveInt(L"Ratio", g_ratio);
    SaveInt(L"Eco", g_eco ? 1 : 0);
    SaveInt(L"ShowTip", g_showTip ? 1 : 0);
    SaveInt(L"CpuPriority", g_cfgCpuPrio);
    SaveString(L"CpuAffinityMask", U64ToStr(g_cfgAffMask));
    SaveString(L"CpuTopology", g_topoSig);
    SaveString(L"Language", LangName(g_langSetting));
    SaveInt(L"GpuPriority", g_cfgGpuPrio);
    SaveInt(L"IoPriority", g_cfgIoPrio);
    SaveWindowState();
    SaveString(L"ClientPath", GetCachedPath());
    SaveString(L"ClientArgs", GetCachedArgs());
    SaveOverlaySettings();
}

static void LoadSettings() {
    g_iniPath = ExeDir() + L"\\ClientManager.ini";
    int rawMode = (int)GetPrivateProfileIntW(L"Settings", L"CpuMode", 2, g_iniPath.c_str());
    int enabled = (int)GetPrivateProfileIntW(L"Settings", L"CpuEnabled", 0, g_iniPath.c_str());
    int ratio = (int)GetPrivateProfileIntW(L"Settings", L"Ratio", 95, g_iniPath.c_str());
    int eco = (int)GetPrivateProfileIntW(L"Settings", L"Eco", 1, g_iniPath.c_str());
    if (rawMode < 1 || rawMode > 3) rawMode = 2;
    if (ratio < 1 || ratio > 99) ratio = 95;
    g_cpuEnabled = (enabled != 0);
    g_mode = rawMode;
    g_ratio = ratio;
    g_eco = (eco != 0);
    g_showTip = (GetPrivateProfileIntW(L"Settings", L"ShowTip", 1, g_iniPath.c_str()) != 0);
    g_cfgCpuPrio = std::max(0, std::min(6, (int)GetPrivateProfileIntW(L"Settings", L"CpuPriority", 0, g_iniPath.c_str())));
    g_cfgGpuPrio = std::max(0, std::min(6, (int)GetPrivateProfileIntW(L"Settings", L"GpuPriority", 0, g_iniPath.c_str())));
    g_cfgIoPrio = std::max(0, std::min(4, (int)GetPrivateProfileIntW(L"Settings", L"IoPriority", 0, g_iniPath.c_str())));
    g_borderless = (GetPrivateProfileIntW(L"Settings", L"Borderless", 0, g_iniPath.c_str()) != 0);
    g_locked = (GetPrivateProfileIntW(L"Settings", L"Locked", 0, g_iniPath.c_str()) != 0);
    std::vector<wchar_t> buf(32768);
    buf[0] = 0;
    GetPrivateProfileStringW(L"Settings", L"ClientPath", L"", buf.data(), (DWORD)buf.size(), g_iniPath.c_str());
    SetCachedPath(buf.data());
    buf[0] = 0;
    GetPrivateProfileStringW(L"Settings", L"CpuAffinityMask", L"0", buf.data(), 64, g_iniPath.c_str());
    g_cfgAffMask = StrToU64(buf.data());
    buf[0] = 0;
    GetPrivateProfileStringW(L"Settings", L"CpuTopology", L"", buf.data(), 512, g_iniPath.c_str());
    if (g_cfgAffMask != 0 && g_topoSig != buf.data()) {   // 設定檔是在不同的 CPU / 核心配置下存的：親和性不能直接沿用
        g_cfgAffMask = 0;
        g_affReset = true;
    }
    buf[0] = 0;
    GetPrivateProfileStringW(L"Settings", L"Language", L"auto", buf.data(), 32, g_iniPath.c_str());
    g_langSetting = LangFromName(buf.data());
    LoadOverlaySettings();
    buf[0] = 0;
    GetPrivateProfileStringW(L"Settings", L"ClientArgs", L"", buf.data(), (DWORD)buf.size(), g_iniPath.c_str());
    {
        std::lock_guard<std::mutex> lk(g_pathMtx);
        g_cachedArgs = buf.data();
    }
}

static void SetCfg(std::atomic<int>& v, const wchar_t* key, int val) {
    v = val;
    SaveInt(key, val);
}

static void SetMode(int m) {
    g_mode = m;
    SaveInt(L"CpuMode", m);
    WakeEngine();
}

// ---------------------------------------------------------------------------
//  行程 / 視窗查詢
// ---------------------------------------------------------------------------
static std::vector<DWORD> GetClientPids() {
    std::vector<DWORD> pids;
    HANDLE snap = CreateToolhelp32Snapshot(TH32CS_SNAPPROCESS, 0);
    if (snap == INVALID_HANDLE_VALUE) return pids;
    PROCESSENTRY32W e;
    e.dwSize = sizeof(e);
    if (Process32FirstW(snap, &e)) {
        do {
            if (_wcsicmp(e.szExeFile, L"client.exe") == 0) pids.push_back(e.th32ProcessID);
        } while (Process32NextW(snap, &e));
    }
    CloseHandle(snap);
    return pids;
}

struct EnumCtx { DWORD pid; HWND best; long long bestArea; bool bestIsMabi; };

static BOOL CALLBACK EnumProc(HWND h, LPARAM lp) {
    EnumCtx* c = (EnumCtx*)lp;
    DWORD p = 0;
    GetWindowThreadProcessId(h, &p);
    if (p != c->pid) return TRUE;
    if (!IsWindowVisible(h)) return TRUE;
    if (GetWindow(h, GW_OWNER) != NULL) return TRUE;
    wchar_t cls[64];
    cls[0] = 0;
    GetClassNameW(h, cls, 64);
    RECT r;
    GetWindowRect(h, &r);
    long long area = (long long)(r.right - r.left) * (long long)(r.bottom - r.top);
    bool mabi = (_wcsicmp(cls, L"Mabinogi") == 0);
    if (c->best == NULL || (mabi && !c->bestIsMabi) || (mabi == c->bestIsMabi && area > c->bestArea)) {
        c->best = h;
        c->bestArea = area;
        c->bestIsMabi = mabi;
    }
    return TRUE;
}

// 取得某個 Client.exe 的主視窗 (優先 class "Mabinogi"，否則取面積最大的頂層可見視窗)
static HWND FindMainWindow(DWORD pid) {
    EnumCtx c;
    c.pid = pid;
    c.best = NULL;
    c.bestArea = -1;
    c.bestIsMabi = false;
    EnumWindows(EnumProc, (LPARAM)&c);
    return c.best;
}

static std::vector<HWND> GetGameWindows() {
    std::vector<HWND> v;
    std::vector<DWORD> pids = GetClientPids();
    for (size_t i = 0; i < pids.size(); ++i) {
        HWND h = FindMainWindow(pids[i]);
        if (h) v.push_back(h);
    }
    return v;
}

// ---------------------------------------------------------------------------
//  權限 / 啟動遊戲
// ---------------------------------------------------------------------------
static bool IsTokenElevated(HANDLE tok) {
    TOKEN_ELEVATION te;
    DWORD ret = 0;
    if (GetTokenInformation(tok, TokenElevation, &te, sizeof(te), &ret)) return te.TokenIsElevated != 0;
    return false;
}

static bool IsSelfElevated() {
    HANDLE t = NULL;
    bool r = false;
    if (OpenProcessToken(GetCurrentProcess(), TOKEN_QUERY, &t)) {
        r = IsTokenElevated(t);
        CloseHandle(t);
    }
    return r;
}

static bool IsProcessElevated(HANDLE hProc) {
    HANDLE t = NULL;
    bool r = false;
    if (OpenProcessToken(hProc, TOKEN_QUERY, &t)) {
        r = IsTokenElevated(t);
        CloseHandle(t);
    }
    return r;
}

static bool EnablePrivilege(const wchar_t* name) {
    HANDLE tok = NULL;
    if (!OpenProcessToken(GetCurrentProcess(), TOKEN_ADJUST_PRIVILEGES | TOKEN_QUERY, &tok)) return false;
    TOKEN_PRIVILEGES tp;
    tp.PrivilegeCount = 1;
    tp.Privileges[0].Attributes = SE_PRIVILEGE_ENABLED;
    bool ok = false;
    if (LookupPrivilegeValueW(NULL, name, &tp.Privileges[0].Luid)) {
        AdjustTokenPrivileges(tok, FALSE, &tp, sizeof(tp), NULL, NULL);
        ok = (GetLastError() == ERROR_SUCCESS);
    }
    CloseHandle(tok);
    return ok;
}

// 以桌面 shell (explorer) 的一般權限啟動，避免遊戲被迫繼承本工具的管理員權限
static bool LaunchDeElevated(const std::wstring& path, const std::wstring& cmd, const std::wstring& dir) {
    HWND shell = GetShellWindow();
    if (!shell) return false;
    DWORD spid = 0;
    GetWindowThreadProcessId(shell, &spid);
    if (!spid) return false;
    EnablePrivilege(L"SeImpersonatePrivilege");
    HANDLE hp = OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION, FALSE, spid);
    if (!hp) return false;
    HANDLE ht = NULL;
    HANDLE hprim = NULL;
    bool ok = false;
    if (OpenProcessToken(hp, TOKEN_DUPLICATE, &ht)) {
        if (DuplicateTokenEx(ht, TOKEN_ASSIGN_PRIMARY | TOKEN_DUPLICATE | TOKEN_QUERY | TOKEN_ADJUST_DEFAULT | TOKEN_ADJUST_SESSIONID,
                             NULL, SecurityImpersonation, TokenPrimary, &hprim)) {
            STARTUPINFOW si;
            ZeroMemory(&si, sizeof(si));
            si.cb = sizeof(si);
            PROCESS_INFORMATION pi;
            ZeroMemory(&pi, sizeof(pi));
            std::vector<wchar_t> buf(cmd.begin(), cmd.end());
            buf.push_back(0);
            if (CreateProcessWithTokenW(hprim, 0, path.c_str(), buf.data(), 0, NULL, dir.c_str(), &si, &pi)) {
                CloseHandle(pi.hProcess);
                CloseHandle(pi.hThread);
                ok = true;
            }
            CloseHandle(hprim);
        }
        CloseHandle(ht);
    }
    CloseHandle(hp);
    return ok;
}

static bool LaunchProcess(const std::wstring& path, const std::wstring& args, const std::wstring& dir, bool deElevate, DWORD* err) {
    std::wstring cmd = L"\"" + path + L"\"";
    if (!args.empty()) cmd += L" " + args;
    if (deElevate && IsSelfElevated()) {
        if (LaunchDeElevated(path, cmd, dir)) return true;   // 失敗 (例如啟動器需要管理員) 則退回一般啟動
    }
    STARTUPINFOW si;
    ZeroMemory(&si, sizeof(si));
    si.cb = sizeof(si);
    PROCESS_INFORMATION pi;
    ZeroMemory(&pi, sizeof(pi));
    std::vector<wchar_t> buf(cmd.begin(), cmd.end());
    buf.push_back(0);
    if (CreateProcessW(path.c_str(), buf.data(), NULL, NULL, FALSE, 0, NULL, dir.empty() ? NULL : dir.c_str(), &si, &pi)) {
        CloseHandle(pi.hProcess);
        CloseHandle(pi.hThread);
        return true;
    }
    if (err) *err = GetLastError();
    return false;
}

// ---------------------------------------------------------------------------
//  Client.exe 資訊 (路徑 / 原始參數 / 是否管理員)
// ---------------------------------------------------------------------------
struct ClientInfo { std::wstring path; std::wstring args; bool elevated; bool found; };

static std::wstring ArgsFromCmdline(const std::wstring& cmd) {
    size_t i = 0;
    while (i < cmd.size() && cmd[i] == L' ') ++i;
    if (i >= cmd.size()) return L"";
    if (cmd[i] == L'"') {
        size_t j = cmd.find(L'"', i + 1);
        if (j == std::wstring::npos) return L"";
        i = j + 1;
    } else {
        size_t j = cmd.find(L' ', i);
        if (j == std::wstring::npos) return L"";
        i = j;
    }
    while (i < cmd.size() && cmd[i] == L' ') ++i;
    return cmd.substr(i);
}

static ClientInfo QueryClientInfo() {
    ClientInfo ci;
    ci.elevated = false;
    ci.found = false;
    std::vector<DWORD> pids = GetClientPids();
    if (pids.empty()) return ci;
    HANDLE h = OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION, FALSE, pids[0]);
    if (!h) return ci;
    wchar_t buf[1024];
    DWORD len = 1024;
    if (QueryFullProcessImageNameW(h, 0, buf, &len)) {
        ci.path.assign(buf, len);
        ci.found = true;
    }
    ci.elevated = IsProcessElevated(h);
    if (g_NtQuery) {
        std::vector<BYTE> mem(2048);
        for (int i = 0; i < 3; ++i) {
            ULONG ret = 0;
            NtStatus st = g_NtQuery(h, 60 /* ProcessCommandLineInformation */, mem.data(), (ULONG)mem.size(), &ret);
            if (st >= 0) {
                UnicodeStr* us = (UnicodeStr*)mem.data();
                if (us->Buffer && us->Length) {
                    std::wstring cmd(us->Buffer, us->Length / sizeof(wchar_t));
                    ci.args = ArgsFromCmdline(cmd);
                }
                break;
            }
            if (ret > mem.size()) mem.resize(ret);
            else mem.resize(mem.size() * 2);
        }
    }
    CloseHandle(h);
    return ci;
}

// 遊戲沒在執行時使用的路徑：最後一次記住的路徑 → C:\Nexon\Mabinogi\Client.exe
static std::wstring GetValidGamePath() {
    std::wstring cached = GetCachedPath();
    if (!cached.empty() && FileExists(cached)) return cached;
    const std::wstring fallback = L"C:\\Nexon\\Mabinogi\\Client.exe";
    if (FileExists(fallback)) return fallback;
    return L"";
}

// 偵測到新的 Client.exe 行程就記住它的路徑與啟動參數 (行程換了才重新查詢)
static void RememberClientInfo(const std::vector<DWORD>& pids) {
    if (pids.empty()) return;
    if (pids[0] == g_cachedPid) return;
    ClientInfo ci = QueryClientInfo();
    if (ci.found) {
        g_cachedPid = pids[0];
        UpdateClientCache(ci.path, ci.args);
    }
}

static void TerminateAllClients(DWORD waitMs) {
    std::vector<DWORD> pids = GetClientPids();
    std::vector<HANDLE> hs;
    for (size_t i = 0; i < pids.size(); ++i) {
        HANDLE h = OpenProcess(PROCESS_TERMINATE | SYNCHRONIZE, FALSE, pids[i]);
        if (h) {
            TerminateProcess(h, 0);
            hs.push_back(h);
        }
    }
    if (waitMs && !hs.empty()) {
        DWORD n = (DWORD)std::min<size_t>(hs.size(), (size_t)MAXIMUM_WAIT_OBJECTS);
        WaitForMultipleObjects(n, hs.data(), TRUE, waitMs);
    }
    for (size_t i = 0; i < hs.size(); ++i) CloseHandle(hs[i]);
}

static void RestartWorker(bool viaLauncher) {
    ClientInfo ci = QueryClientInfo();
    std::wstring clientPath;
    std::wstring args;
    if (ci.found && FileExists(ci.path)) {
        clientPath = ci.path;
        args = ci.args;
        UpdateClientCache(clientPath, args);
    } else {
        clientPath = GetValidGamePath();   // 最後一次記住的路徑 → C:\Nexon\Mabinogi\Client.exe
        args = GetCachedArgs();            // 最後一次記住的啟動參數
    }
    if (clientPath.empty() || !FileExists(clientPath)) {
        Notify(T(S_NO_GAME_PATH));
        return;
    }
    std::wstring dir = DirOf(clientPath);
    std::wstring target = clientPath;
    if (viaLauncher) {
        target = dir + L"\\Mabinogi.exe";
        if (!FileExists(target)) target = dir + L"\\mabinogi.exe";
        if (!FileExists(target)) {
            Notify(T(S_NO_LAUNCHER));
            return;
        }
        args.clear();
    }
    bool deElevate = ci.found ? !ci.elevated : false;   // 遊戲執行中時維持原本的權限等級
    g_fastUntil = GetTickCount64() + 30000;   // 重啟後 30 秒內密集偵測，新視窗一出現就立刻套用設定
    TerminateAllClients(5000);
    Sleep(300);
    DWORD err = 0;
    if (!LaunchProcess(target, args, dir, deElevate, &err)) {
        wchar_t b[96];
        wsprintfW(b, T(S_RESTART_FAIL), (unsigned long)err);
        Notify(b);
    }
}

static void StartRestart(bool viaLauncher) {
    if (g_restarting.exchange(true)) return;
    std::thread([viaLauncher]() {
        RestartWorker(viaLauncher);
        g_restarting = false;
    }).detach();
}

// ---------------------------------------------------------------------------
//  視窗管理 (無邊框 / 鎖定 / 重置)
// ---------------------------------------------------------------------------
// ---------------------------------------------------------------------------
//  程序優先權 / 親和性 (類似 Process Lasso)：偵測到 Client.exe 啟動後自動套用
// ---------------------------------------------------------------------------
static DWORD PrioClassFromLevel(int lv) {
    switch (lv) {
    case 1: return IDLE_PRIORITY_CLASS;
    case 2: return BELOW_NORMAL_PRIORITY_CLASS;
    case 3: return NORMAL_PRIORITY_CLASS;
    case 4: return ABOVE_NORMAL_PRIORITY_CLASS;
    case 5: return HIGH_PRIORITY_CLASS;
    case 6: return REALTIME_PRIORITY_CLASS;
    }
    return 0;
}

// 偵測核心類型 (大核 / 小核 / 超執行緒)：效率等級最高的是大核 (P-core)；非混合架構時全部視為大核
static void InitCpuTopologyImpl() {
    DWORD_PTR procMask = 0, sysMask = 0;
    GetProcessAffinityMask(GetCurrentProcess(), &procMask, &sysMask);
    g_maskAll = sysMask;
    g_maskP = g_maskPnoHT = g_maskE = sysMask;
    g_coreCount = 0;
    for (int i = 0; i < 64; ++i) {
        if ((sysMask >> i) & 1) g_coreCount = i + 1;
        g_coreType[i] = 0;
    }
    DWORD len = 0;
    GetLogicalProcessorInformationEx(RelationProcessorCore, NULL, &len);
    if (!len) return;
    std::vector<BYTE> buf(len);
    if (!GetLogicalProcessorInformationEx(RelationProcessorCore, (PSYSTEM_LOGICAL_PROCESSOR_INFORMATION_EX)buf.data(), &len)) return;
    struct CoreInfo { BYTE eff; DWORD_PTR mask; };
    std::vector<CoreInfo> cores;
    BYTE maxEff = 0, minEff = 255;
    for (DWORD off = 0; off < len;) {
        PSYSTEM_LOGICAL_PROCESSOR_INFORMATION_EX p = (PSYSTEM_LOGICAL_PROCESSOR_INFORMATION_EX)(buf.data() + off);
        if (p->Size == 0) break;
        if (p->Relationship == RelationProcessorCore && p->Processor.GroupCount >= 1 && p->Processor.GroupMask[0].Group == 0) {
            CoreInfo c;
            c.eff = p->Processor.EfficiencyClass;
            c.mask = p->Processor.GroupMask[0].Mask;
            cores.push_back(c);
            if (c.eff > maxEff) maxEff = c.eff;
            if (c.eff < minEff) minEff = c.eff;
        }
        off += p->Size;
    }
    if (cores.empty()) return;
    g_hybrid = (maxEff != minEff);
    DWORD_PTR mp = 0, mpn = 0, me = 0;
    for (size_t i = 0; i < cores.size(); ++i) {
        bool isP = !g_hybrid || cores[i].eff == maxEff;
        bool first = true;
        for (int b = 0; b < 64; ++b) {
            if (!((cores[i].mask >> b) & 1)) continue;
            int type;
            if (g_hybrid) type = isP ? (first ? 1 : 2) : (first ? 3 : 4);
            else type = first ? 5 : 6;
            g_coreType[b] = type;
            if (isP && first) mpn |= ((DWORD_PTR)1 << b);
            first = false;
        }
        if (isP) mp |= cores[i].mask;
        else me |= cores[i].mask;
    }
    if (mpn) g_maskPnoHT = mpn & sysMask;   // 大小核與一般 CPU 都需要：每顆 (大核) 實體核心的第一個執行緒
    if (g_hybrid) {
        if (mp) g_maskP = mp & sysMask;
        if (me) g_maskE = me & sysMask;
    }
}

static void InitCpuTopology() {
    DetectCpuVendor();
    InitCpuTopologyImpl();
    // 核心配置簽章：換到不同 CPU (或在 BIOS 改了核心 / 超執行緒設定) 時會不同
    g_topoSig = L"all=" + U64ToStr((unsigned long long)g_maskAll) + L";p=" + U64ToStr((unsigned long long)g_maskP) +
                L";e=" + U64ToStr((unsigned long long)g_maskE) + L";h=" + std::wstring(g_hybrid ? L"1" : L"0");
}

static int LevelFromPrioClass(DWORD c) {
    switch (c) {
    case IDLE_PRIORITY_CLASS: return 1;
    case BELOW_NORMAL_PRIORITY_CLASS: return 2;
    case NORMAL_PRIORITY_CLASS: return 3;
    case ABOVE_NORMAL_PRIORITY_CLASS: return 4;
    case HIGH_PRIORITY_CLASS: return 5;
    case REALTIME_PRIORITY_CLASS: return 6;
    }
    return 0;
}

// GPU 優先權：依序嘗試不同的存取權限 (部分系統需要較高權限才能讀寫)
static int ReadGpuClassPid(DWORD pid, LONG* status) {
    if (!g_D3dkmtGetPrio) {
        if (status) *status = (LONG)0xC0000002;   // STATUS_NOT_IMPLEMENTED：此系統沒有提供讀取介面
        return -1;
    }
    const DWORD masks[3] = { PROCESS_QUERY_INFORMATION, PROCESS_QUERY_INFORMATION | PROCESS_SET_INFORMATION, PROCESS_ALL_ACCESS };
    LONG last = (LONG)0xC0000022;   // STATUS_ACCESS_DENIED
    for (int i = 0; i < 3; ++i) {
        HANDLE h = OpenProcess(masks[i], FALSE, pid);
        if (!h) continue;
        int c = -1;
        LONG st = g_D3dkmtGetPrio(h, &c);
        CloseHandle(h);
        last = st;
        if (st >= 0 && c >= 0 && c <= 5) {
            if (status) *status = 0;
            return c;
        }
    }
    if (status) *status = last;
    return -1;
}

static void WriteGpuClassPid(DWORD pid, int cls) {
    if (!g_D3dkmtSetPrio || cls < 0) return;
    const DWORD masks[2] = { PROCESS_SET_INFORMATION | PROCESS_QUERY_LIMITED_INFORMATION, PROCESS_ALL_ACCESS };
    for (int i = 0; i < 2; ++i) {
        HANDLE h = OpenProcess(masks[i], FALSE, pid);
        if (!h) continue;
        LONG st = g_D3dkmtSetPrio(h, cls);
        CloseHandle(h);
        if (st >= 0) return;
    }
}

static bool IsLowered(DWORD pid) {
    std::lock_guard<std::mutex> lk(g_loweredMtx);
    return g_lowered.count(pid) != 0;
}

static void MarkLowered(DWORD pid, bool on) {
    std::lock_guard<std::mutex> lk(g_loweredMtx);
    if (on) g_lowered.insert(pid);
    else g_lowered.erase(pid);
}

static void SetAffMask(unsigned long long m);

// 第一次偵測到遊戲時，把「尚未設定」的項目從執行中的遊戲讀出來並存進設定檔
static void InitBaseFromClient(DWORD pid) {
    bool needCp = (g_cfgCpuPrio == 0), needAff = (g_cfgAffMask == 0), needGpu = (g_cfgGpuPrio == 0), needIo = (g_cfgIoPrio == 0);
    if (!needCp && !needAff && !needGpu && !needIo) return;
    HANDLE h = OpenProcess(PROCESS_QUERY_INFORMATION | PROCESS_QUERY_LIMITED_INFORMATION, FALSE, pid);
    if (!h) return;
    if (needCp) {
        DWORD c = GetPriorityClass(h);
        bool ambiguous = (c == IDLE_PRIORITY_CLASS && g_cpuEnabled && g_eco);   // 可能是本工具剛降下去的，無法判斷
        int lv = LevelFromPrioClass(c);
        if (lv && !ambiguous) SetCfg(g_cfgCpuPrio, L"CpuPriority", lv);
    }
    if (needAff) {
        DWORD_PTR pm = 0, sm = 0;
        if (GetProcessAffinityMask(h, &pm, &sm) && pm) SetAffMask((unsigned long long)pm);
    }
    if (needGpu) {
        int c = ReadGpuClassPid(pid, NULL);
        if (c >= 0) SetCfg(g_cfgGpuPrio, L"GpuPriority", c + 1);
    }
    if (needIo && g_NtQuery) {
        ULONG v = 0, ret = 0;
        if (g_NtQuery(h, 33 /* ProcessIoPriority */, &v, sizeof(v), &ret) >= 0) SetCfg(g_cfgIoPrio, L"IoPriority", (v >= 3) ? 4 : (int)v + 1);
    }
    CloseHandle(h);
}

static void ApplyBaseSettings(DWORD pid) {
    int cp = g_cfgCpuPrio, gp = g_cfgGpuPrio, io = g_cfgIoPrio;
    unsigned long long am = g_cfgAffMask;
    if (!cp && !gp && !io && !am) return;
    HANDLE h = OpenProcess(PROCESS_SET_INFORMATION | PROCESS_QUERY_LIMITED_INFORMATION, FALSE, pid);
    if (!h) return;
    // 限制中 (已降低優先權) 時不套用 CPU / GPU / I/O 優先權，解除限制時會還原成設定值
    bool low = IsLowered(pid);
    if (cp && !low) {
        DWORD cls = PrioClassFromLevel(cp);
        if (SetPriorityClass(h, cls)) {
            g_prioErr = 0;
        } else {
            DWORD e = GetLastError();
            if (cls == REALTIME_PRIORITY_CLASS) SetPriorityClass(h, HIGH_PRIORITY_CLASS);   // 無法設為即時時，至少設為「高」，避免停在低優先權
            g_prioErr = e;
        }
    }
    if (am) {
        DWORD_PTR m = (DWORD_PTR)(am & (unsigned long long)g_maskAll);
        if (m) SetProcessAffinityMask(h, m);
    }
    if (gp && !low) WriteGpuClassPid(pid, gp - 1);   // 0=Idle ... 5=Realtime
    if (io && !low && g_NtSetInfo) {
        ULONG v = (ULONG)(io - 1);                            // 0=極低 1=低 2=正常 3=高
        g_NtSetInfo(h, 33 /* ProcessIoPriority */, &v, sizeof(v));
    }
    CloseHandle(h);
}

static void ApplyBaseToAll() {
    std::vector<DWORD> pids = GetClientPids();
    for (size_t i = 0; i < pids.size(); ++i) ApplyBaseSettings(pids[i]);
}

static void SetAffMask(unsigned long long m) {
    g_cfgAffMask = m;
    SaveString(L"CpuAffinityMask", U64ToStr(m));
    SaveString(L"CpuTopology", g_topoSig);
    ApplyBaseToAll();
}

struct WinState { RECT client; bool hasClient; bool managed; int stable; RECT last; bool lockDone; ULONGLONG enforceUntil; };
static std::map<HWND, WinState> g_wins;   // 只在 UI 執行緒使用

static WinState& GetState(HWND h) {
    std::map<HWND, WinState>::iterator it = g_wins.find(h);
    if (it == g_wins.end()) {
        WinState ws;
        ZeroMemory(&ws, sizeof(ws));
        GetWindowRect(h, &ws.last);
        it = g_wins.insert(std::make_pair(h, ws)).first;
    }
    return it->second;
}

static bool HasCaption(HWND h) {
    LONG_PTR s = GetWindowLongPtrW(h, GWL_STYLE);
    return (s & WS_CAPTION) == WS_CAPTION;
}

static void SaveClient(HWND h, WinState& ws) {
    if (IsIconic(h) || IsZoomed(h)) return;
    RECT c;
    POINT p;
    p.x = 0;
    p.y = 0;
    GetClientRect(h, &c);
    ClientToScreen(h, &p);
    if (c.right > 100 && c.bottom > 100) {
        ws.client.left = p.x;
        ws.client.top = p.y;
        ws.client.right = p.x + c.right;
        ws.client.bottom = p.y + c.bottom;
        ws.hasClient = true;
    }
}

static RECT DefaultClientRect(HWND h) {
    MONITORINFO mi;
    ZeroMemory(&mi, sizeof(mi));
    mi.cbSize = sizeof(mi);
    HMONITOR m = MonitorFromWindow(h, MONITOR_DEFAULTTONEAREST);
    GetMonitorInfoW(m, &mi);
    const int w = 1280, hh = 720;
    RECT r;
    r.left = mi.rcWork.left + ((mi.rcWork.right - mi.rcWork.left) - w) / 2;
    r.top = mi.rcWork.top + ((mi.rcWork.bottom - mi.rcWork.top) - hh) / 2;
    r.right = r.left + w;
    r.bottom = r.top + hh;
    return r;
}

// 把「客戶區」放到指定的螢幕座標：先用 AdjustWindowRectEx 估算，再讀回實際客戶區做校正
static void PlaceClient(HWND h, const RECT& want, LONG_PTR style, LONG_PTR ex) {
    RECT o = want;
    AdjustWindowRectEx(&o, (DWORD)style, FALSE, (DWORD)ex);
    SetWindowPos(h, NULL, o.left, o.top, o.right - o.left, o.bottom - o.top,
                 SWP_NOZORDER | SWP_NOACTIVATE | SWP_FRAMECHANGED | SWP_SHOWWINDOW);
    for (int i = 0; i < 3; ++i) {
        RECT c;
        POINT p;
        p.x = 0;
        p.y = 0;
        GetClientRect(h, &c);
        ClientToScreen(h, &p);
        RECT a;
        a.left = p.x;
        a.top = p.y;
        a.right = p.x + c.right;
        a.bottom = p.y + c.bottom;
        if (a.left == want.left && a.top == want.top && a.right == want.right && a.bottom == want.bottom) break;
        RECT w;
        GetWindowRect(h, &w);
        SetWindowPos(h, NULL,
                     w.left + (want.left - a.left),
                     w.top + (want.top - a.top),
                     (w.right - w.left) + ((want.right - want.left) - (a.right - a.left)),
                     (w.bottom - w.top) + ((want.bottom - want.top) - (a.bottom - a.top)),
                     SWP_NOZORDER | SWP_NOACTIVATE);
    }
}

// 改變樣式但保持「客戶區」大小與位置不變 (反覆鎖定 / 解鎖不會越變越小)
static void SetStyleKeepClient(HWND h, LONG_PTR newStyle) {
    LONG_PTR ex = GetWindowLongPtrW(h, GWL_EXSTYLE);
    bool normal = !IsIconic(h) && !IsZoomed(h);
    RECT want;
    want.left = want.top = want.right = want.bottom = 0;
    if (normal) {
        RECT cr;
        POINT tl;
        tl.x = 0;
        tl.y = 0;
        GetClientRect(h, &cr);
        ClientToScreen(h, &tl);
        want.left = tl.x;
        want.top = tl.y;
        want.right = tl.x + cr.right;
        want.bottom = tl.y + cr.bottom;
    }
    SetWindowLongPtrW(h, GWL_STYLE, newStyle);
    if (normal && want.right > want.left && want.bottom > want.top) {
        PlaceClient(h, want, newStyle, ex);
    } else {
        SetWindowPos(h, NULL, 0, 0, 0, 0,
                     SWP_NOMOVE | SWP_NOSIZE | SWP_NOZORDER | SWP_NOACTIVATE | SWP_FRAMECHANGED);
    }
}

// 鎖定位置：記錄鎖定時的視窗左上角、「移動」系統選單灰階；使用者拖曳時取消並回到原位
static void UpdateLockPos(HWND h) {
    RECT r;
    GetWindowRect(h, &r);
    POINT p;
    p.x = r.left;
    p.y = r.top;
    g_lockPos[h] = p;
}

static void SetMoveMenu(HWND h, bool enabled) {
    HMENU sm = GetSystemMenu(h, FALSE);
    if (sm) EnableMenuItem(sm, SC_MOVE, MF_BYCOMMAND | (enabled ? MF_ENABLED : MF_GRAYED));
}

static void EnsureLockState(HWND h) {
    if (g_lockPos.find(h) == g_lockPos.end()) UpdateLockPos(h);
    SetMoveMenu(h, false);
}

// 系統每次開啟標題列選單都會重設「移動」的狀態：偵測到選單開啟就立刻變灰，
// 並在接下來約 0.25 秒內每 30 毫秒再補一次 (遊戲自己處理選單時可能晚一步重設)
static void RegrayAllLocked() {
    if (!g_locked) return;
    for (std::map<HWND, POINT>::iterator it = g_lockPos.begin(); it != g_lockPos.end(); ++it) SetMoveMenu(it->first, false);
    if (g_gameHwnd && g_lockPos.find(g_gameHwnd) == g_lockPos.end()) SetMoveMenu(g_gameHwnd, false);
}

static void StartRegrayBurst() {
    g_regrayLeft = 8;
    if (g_hWnd) SetTimer(g_hWnd, 4, 30, NULL);
}

static void ApplyLock(HWND h, bool lock) {
    if (!HasCaption(h)) return;   // 無邊框狀態下沒有邊框可鎖，還原時才會套用
    LONG_PTR s = GetWindowLongPtrW(h, GWL_STYLE);
    if (lock) s &= ~(LONG_PTR)(WS_THICKFRAME | WS_MAXIMIZEBOX);
    else s |= (LONG_PTR)(WS_THICKFRAME | WS_MAXIMIZEBOX);
    SetStyleKeepClient(h, s);
    if (lock) {
        UpdateLockPos(h);
        SetMoveMenu(h, false);
    } else {
        g_lockPos.erase(h);
        SetMoveMenu(h, true);
    }
}

static void ApplyBorderless(HWND h) {
    if (IsIconic(h) || IsZoomed(h)) ShowWindow(h, SW_RESTORE);
    LONG_PTR s = GetWindowLongPtrW(h, GWL_STYLE);
    s &= ~(LONG_PTR)(WS_CAPTION | WS_THICKFRAME);
    SetWindowLongPtrW(h, GWL_STYLE, s);
    MONITORINFO mi;
    ZeroMemory(&mi, sizeof(mi));
    mi.cbSize = sizeof(mi);
    HMONITOR m = MonitorFromWindow(h, MONITOR_DEFAULTTONEAREST);
    GetMonitorInfoW(m, &mi);
    SetWindowPos(h, HWND_TOP, mi.rcWork.left, mi.rcWork.top,
                 mi.rcWork.right - mi.rcWork.left, mi.rcWork.bottom - mi.rcWork.top,
                 SWP_FRAMECHANGED | SWP_NOACTIVATE | SWP_SHOWWINDOW);
}

static void RestoreWindow(HWND h, WinState& ws) {
    if (IsIconic(h) || IsZoomed(h)) ShowWindow(h, SW_RESTORE);
    LONG_PTR s = GetWindowLongPtrW(h, GWL_STYLE) | (LONG_PTR)(WS_CAPTION | WS_THICKFRAME | WS_MAXIMIZEBOX);
    if (g_locked) s &= ~(LONG_PTR)(WS_THICKFRAME | WS_MAXIMIZEBOX);
    LONG_PTR ex = GetWindowLongPtrW(h, GWL_EXSTYLE);
    SetWindowLongPtrW(h, GWL_STYLE, s);
    RECT c = ws.hasClient ? ws.client : DefaultClientRect(h);
    PlaceClient(h, c, s, ex);
    if (g_locked) {
        UpdateLockPos(h);
        SetMoveMenu(h, false);
    } else {
        g_lockPos.erase(h);
        SetMoveMenu(h, true);
    }
}

static void ToggleBorderless() {
    std::vector<HWND> wins = GetGameWindows();
    if (wins.empty()) {
        ShowNoGameDialog();
        return;
    }
    LimitPause lp;
    for (size_t i = 0; i < wins.size(); ++i) {
        HWND h = wins[i];
        WinState& ws = GetState(h);
        ws.managed = true;
        if (HasCaption(h)) {
            if (IsIconic(h) || IsZoomed(h)) ShowWindow(h, SW_RESTORE);
            SaveClient(h, ws);
            ApplyBorderless(h);
            g_borderless = true;
        } else {
            RestoreWindow(h, ws);
            g_borderless = false;
        }
    }
    SaveWindowState();
}

static void ResetWindow() {
    std::vector<HWND> wins = GetGameWindows();
    if (wins.empty()) {
        ShowNoGameDialog();
        return;
    }
    LimitPause lp;
    for (size_t i = 0; i < wins.size(); ++i) {
        WinState& ws = GetState(wins[i]);
        ws.managed = true;
        RestoreWindow(wins[i], ws);
    }
    g_borderless = false;
    SaveWindowState();
}

static void ToggleLock() {
    std::vector<HWND> wins = GetGameWindows();
    if (wins.empty() && !g_locked) {
        ShowNoGameDialog();
        return;
    }
    g_locked = !g_locked;
    LimitPause lp;
    for (size_t i = 0; i < wins.size(); ++i) ApplyLock(wins[i], g_locked);
    if (!g_locked) g_lockPos.clear();
    SaveWindowState();
}

// 工具啟動時：同步遊戲現況到選單勾選狀態
static void InitialSync() {
    RememberClientInfo(GetClientPids());
    std::vector<HWND> wins = GetGameWindows();
    if (wins.empty()) return;   // 遊戲沒開：沿用設定檔記錄的無邊框 / 鎖定狀態
    g_borderless = false;
    for (size_t i = 0; i < wins.size(); ++i) {
        HWND h = wins[i];
        WinState& ws = GetState(h);
        ws.managed = true;
        if (HasCaption(h)) {
            SaveClient(h, ws);
            LONG_PTR st = GetWindowLongPtrW(h, GWL_STYLE);
            g_locked = ((st & WS_THICKFRAME) == 0);
            if (g_locked) EnsureLockState(h);
        } else {
            g_borderless = true;
        }
    }
}

// 每 500ms：偵測「新出現的遊戲視窗」(重啟遊戲後)，穩定後自動套用目前的無邊框/鎖定狀態
static void SyncWindows() {
    ULONGLONG now = GetTickCount64();
    std::vector<DWORD> pids = GetClientPids();
    RememberClientInfo(pids);
    DWORD newGamePid = pids.empty() ? 0 : pids[0];
    if (g_gamePid != newGamePid) {
        g_gamePid = newGamePid;
        if (g_monWake) SetEvent(g_monWake);   // 取樣執行緒依新的遊戲行程重新開始
    }
    g_fpsPid = newGamePid;
    UpdateGameHook();
    g_gameHwnd = NULL;
    bool busy = (now < g_fastUntil);   // 重啟遊戲後的一段時間內使用密集偵測

    // 優先權 / 親和性 / GPU / I/O：新偵測到的 Client 立即套用；偵測後 15 秒內每個週期確認一次，
    // 之後每 2 秒確認一次 (被遊戲或啟動器改回去時會再套用；限制中已降低優先權的行程不會被覆蓋)
    for (size_t i = 0; i < pids.size(); ++i) {
        std::map<DWORD, BaseTrack>::iterator it = g_base.find(pids[i]);
        if (it == g_base.end()) {
            BaseTrack bt;
            bt.since = now;
            bt.next = now + 2000;
            g_base[pids[i]] = bt;
            InitBaseFromClient(pids[i]);    // 尚未設定的項目：讀取目前值並存檔
            ApplyBaseSettings(pids[i]);     // 其餘：套用設定檔的值
            g_forceRefresh = true;          // 讓 CPU 限制引擎也立刻接手這個新行程
            WakeEngine();
            busy = true;
        } else {
            bool early = (now - it->second.since) < 15000;
            if (early) busy = true;
            if (early || now >= it->second.next) {
                ApplyBaseSettings(pids[i]);
                it->second.next = now + 2000;
            }
        }
    }
    for (std::map<DWORD, BaseTrack>::iterator it = g_base.begin(); it != g_base.end();) {
        if (std::find(pids.begin(), pids.end(), it->first) == pids.end()) it = g_base.erase(it);
        else ++it;
    }

    // 視窗：鎖定大小 / 無邊框
    std::vector<HWND> alive;
    for (size_t i = 0; i < pids.size(); ++i) {
        HWND h = FindMainWindow(pids[i]);
        if (!h) continue;
        alive.push_back(h);
        if (alive.size() == 1) g_gameHwnd = h;
        WinState& ws = GetState(h);
        RECT r;
        GetWindowRect(h, &r);
        bool big = (r.right - r.left) > 100 && (r.bottom - r.top) > 100 && !IsIconic(h);
        bool cap = HasCaption(h);
        if (!ws.managed) {
            busy = true;
            // 鎖定視窗大小：視窗一出現就立即套用 (保持客戶區不變，不需等視窗穩定)
            if (big && cap && g_locked && !g_borderless && !ws.lockDone) {
                LimitPause lp;
                ApplyLock(h, true);
                ws.lockDone = true;
                GetWindowRect(h, &r);
            }
            if (big && EqualRect(&r, &ws.last)) ws.stable++;
            else ws.stable = 0;
            ws.last = r;
            if (ws.stable >= 3) {   // 視窗大小穩定後 (約 0.75 秒) 才記錄原始大小並套用無邊框
                ws.managed = true;
                ws.enforceUntil = now + 20000;
                if (cap) {
                    LimitPause lp;
                    SaveClient(h, ws);
                    if (g_borderless) ApplyBorderless(h);
                    else if (g_locked) ApplyLock(h, true);
                }
            }
        }
        if (g_locked && cap) {
            EnsureLockState(h);   // 持續維持「移動」灰階與鎖定位置記錄
            // 遊戲自己把縮放邊框加回來時，只把樣式改回去 (保持目前的客戶區大小與位置，不會重設視窗大小)
            if (!g_borderless && !IsIconic(h) && (GetWindowLongPtrW(h, GWL_STYLE) & WS_THICKFRAME)) {
                LimitPause lp;
                ApplyLock(h, true);
            }
        }
    }
    for (std::map<HWND, WinState>::iterator it = g_wins.begin(); it != g_wins.end();) {
        if (std::find(alive.begin(), alive.end(), it->first) == alive.end()) {
            g_lockPos.erase(it->first);
            it = g_wins.erase(it);
        } else {
            ++it;
        }
    }
    // 忙碌時 250ms 密集偵測，其餘時間每 1 秒檢查一次，降低閒置 CPU 使用
    UpdateOverlayVisibility();
    UINT want = busy ? kFastMs : kIdleMs;
    if (want != g_syncInterval) {
        g_syncInterval = want;
        SetTimer(g_hWnd, 1, want, NULL);
    }
}

// ---------------------------------------------------------------------------
//  CPU 限制引擎 (BES 風格)
//    * 每個週期內：暫停 N% 時間、執行其餘時間；週期隨比例自動調整 (執行片段至少約 4ms)
//    * 持久化 handle，不在迴圈內反覆 OpenProcess / 建立 Process 物件
//    * 前景判斷以「行程」為單位 (遊戲對話框也算前景)，且用事件即時喚醒
//    * 高解析度計時器 + QPC 補償，避免 Sleep() 的 15.6ms 粒度造成比例不準
//    * 限制期間可選擇同時降為 IDLE 優先權 + EcoQoS (Win11 會移到 E-core)
// ---------------------------------------------------------------------------
struct Target {
    DWORD pid;
    HANDLE h;
    HWND wnd;
    bool suspended;
    bool lowered;
    DWORD oldPrio;
    HWND iconWnd;       // 目前圖示狀態所屬的視窗
    bool iconBlue;      // 遊戲視窗圖示目前是否為藍色版
    HICON origBig, origSmall, blueBig, blueSmall;
    HICON restBig, restSmall;   // 還原時使用的圖示 (原本沒有自己的圖示時，改用視窗類別的圖示)
    int oldGpu, oldIo;          // 限制前的 GPU 優先權 (0..5) / I/O 優先權 (0..3)，-1 = 未知
    bool blueBigOwned, blueSmallOwned;
};

static void WaitMs(double ms) {
    if (ms < 0.2) return;
    if (g_timer) {
        LARGE_INTEGER due;
        due.QuadPart = -(LONGLONG)(ms * 10000.0);
        if (SetWaitableTimer(g_timer, &due, 0, NULL, NULL, FALSE)) {
            HANDLE hs[2] = { g_timer, g_wake };
            WaitForMultipleObjects(2, hs, FALSE, INFINITE);
            return;
        }
    }
    WaitForSingleObject(g_wake, (DWORD)(ms + 0.5));
}

static void CalcSlices(int ratioPct, double* suspendMs, double* cycleMs) {
    double r = (double)std::max(1, std::min(99, ratioPct)) / 100.0;
    const double runMin = 4.0;
    double cycle = runMin / (1.0 - r);
    if (cycle < 25.0) cycle = 25.0;
    if (cycle > 120.0) cycle = 120.0;
    double run = cycle * (1.0 - r);
    if (run < 2.0) run = 2.0;
    *cycleMs = cycle;
    *suspendMs = cycle - run;
}

static void SuspendT(Target& t) {
    if (!t.suspended && g_NtSuspend && g_NtSuspend(t.h) >= 0) t.suspended = true;
}

static void ResumeT(Target& t) {
    if (t.suspended) {
        if (g_NtResume) g_NtResume(t.h);
        t.suspended = false;
    }
}

static void SetEco(HANDLE h, bool on) {
    if (!g_SetProcInfo) return;
    PowerThrottleState s;
    s.Version = 1;
    s.ControlMask = on ? 1 : 0;
    s.StateMask = on ? 1 : 0;
    g_SetProcInfo(h, 4 /* ProcessPowerThrottling */, &s, sizeof(s));
}

static int ReadGpuClass(HANDLE h) {
    int c = -1;
    if (g_D3dkmtGetPrio && g_D3dkmtGetPrio(h, &c) >= 0 && c >= 0 && c <= 5) return c;
    return -1;
}

static int ReadIoHint(HANDLE h) {
    ULONG v = 0, ret = 0;
    if (g_NtQuery && g_NtQuery(h, 33 /* ProcessIoPriority */, &v, sizeof(v), &ret) >= 0) return (v >= 3) ? 3 : (int)v;
    return -1;
}

static void WriteGpuClass(HANDLE h, int c) {
    if (c >= 0 && g_D3dkmtSetPrio) g_D3dkmtSetPrio(h, c);
}

static void WriteIoHint(HANDLE h, int v) {
    if (v >= 0 && g_NtSetInfo) {
        ULONG x = (ULONG)v;
        g_NtSetInfo(h, 33 /* ProcessIoPriority */, &x, sizeof(x));
    }
}

// 限制生效時：CPU 優先權降為 Idle、GPU 優先權降為 Idle、I/O 優先權降為極低，並啟用節能模式
static void LowerT(Target& t) {
    DWORD p = GetPriorityClass(t.h);
    if (p && p != IDLE_PRIORITY_CLASS) t.oldPrio = p;
    t.oldGpu = ReadGpuClass(t.h);
    t.oldIo = ReadIoHint(t.h);
    SetPriorityClass(t.h, IDLE_PRIORITY_CLASS);
    WriteGpuClass(t.h, 0);
    WriteIoHint(t.h, 0);
    SetEco(t.h, true);
    t.lowered = true;
    MarkLowered(t.pid, true);
}

// 解除限制：有設定值就還原成設定值，否則還原成限制前的值
static void RestoreT(Target& t) {
    DWORD cfg = PrioClassFromLevel(g_cfgCpuPrio);
    DWORD back = cfg ? cfg : t.oldPrio;
    if (back) SetPriorityClass(t.h, back);
    int gp = g_cfgGpuPrio;
    WriteGpuClass(t.h, gp ? gp - 1 : t.oldGpu);
    int io = g_cfgIoPrio;
    WriteIoHint(t.h, io ? io - 1 : t.oldIo);
    SetEco(t.h, false);
    t.lowered = false;
    t.oldPrio = 0;
    t.oldGpu = -1;
    t.oldIo = -1;
    MarkLowered(t.pid, false);
}

// 限制中若優先權被其他工具 (例如 Process Lasso) 改回去，再降低一次
static void EnforceLow(Target& t) {
    if (GetPriorityClass(t.h) != IDLE_PRIORITY_CLASS) SetPriorityClass(t.h, IDLE_PRIORITY_CLASS);
}

static HICON CreateBlueIcon(HICON src);

static HICON QueryWndIcon(HWND w, WPARAM type) {
    DWORD_PTR res = 0;
    if (!SendMessageTimeoutW(w, WM_GETICON, type, 0, SMTO_ABORTIFHUNG | SMTO_BLOCK, 300, &res)) return NULL;
    return (HICON)res;
}

static bool SetWndIcon(HWND w, WPARAM type, HICON ic) {
    DWORD_PTR res = 0;
    return SendMessageTimeoutW(w, WM_SETICON, type, (LPARAM)ic, SMTO_ABORTIFHUNG | SMTO_BLOCK, 300, &res) != 0;
}

static void FreeIcons(Target& t) {
    if (t.blueBig && t.blueBigOwned) DestroyIcon(t.blueBig);
    if (t.blueSmall && t.blueSmallOwned) DestroyIcon(t.blueSmall);
    t.blueBig = t.blueSmall = NULL;
    t.blueBigOwned = t.blueSmallOwned = false;
    t.origBig = t.origSmall = NULL;
    t.restBig = t.restSmall = NULL;
    t.iconBlue = false;
    t.iconWnd = NULL;
}

// 用「當初換成藍色的那個視窗」把圖示換回去 (遊戲主視窗的判斷可能隨最小化等狀態改變，所以不能用 t.wnd)
static bool RestoreClientIcon(Target& t) {
    if (!t.iconBlue) return true;
    HWND w = t.iconWnd;
    if (!w || !IsWindow(w)) {
        t.iconBlue = false;
        return true;
    }
    bool ok1 = SetWndIcon(w, ICON_BIG, t.restBig);
    bool ok2 = SetWndIcon(w, ICON_SMALL, t.restSmall);
    if (ok1 && ok2) t.iconBlue = false;
    return ok1 && ok2;   // 失敗時保持藍色狀態，下個週期重試
}

// 限制生效時，把遊戲視窗 (工作列 / 標題列) 的圖示換成自己圖示的藍色版；結束後換回原本的圖示
static void SetClientIconBlue(Target& t, bool blue) {
    if (!blue) {
        RestoreClientIcon(t);
        return;
    }
    if (!t.wnd || !IsWindow(t.wnd)) return;
    if (t.iconWnd != t.wnd) {
        RestoreClientIcon(t);   // 主視窗換了：先把舊視窗換回去
        FreeIcons(t);
        t.iconWnd = t.wnd;
    }
    if (t.iconBlue) return;
    if (!t.blueBig) {
        t.origBig = QueryWndIcon(t.wnd, ICON_BIG);
        t.origSmall = QueryWndIcon(t.wnd, ICON_SMALL);
        HICON baseBig = t.origBig ? t.origBig : (HICON)GetClassLongPtrW(t.wnd, GCLP_HICON);
        HICON baseSmall = t.origSmall ? t.origSmall : (HICON)GetClassLongPtrW(t.wnd, GCLP_HICONSM);
        if (!baseBig) baseBig = baseSmall;
        if (!baseSmall) baseSmall = baseBig;
        t.restBig = baseBig;
        t.restSmall = baseSmall;
        HICON bb = baseBig ? CreateBlueIcon(baseBig) : NULL;
        if (bb && bb != baseBig) {
            t.blueBig = bb;
            t.blueBigOwned = true;
        } else {
            t.blueBig = g_iconBlue;   // 無法調色時改用本工具的藍色圖示
            t.blueBigOwned = false;
        }
        HICON bs = baseSmall ? CreateBlueIcon(baseSmall) : NULL;
        if (bs && bs != baseSmall) {
            t.blueSmall = bs;
            t.blueSmallOwned = true;
        } else {
            t.blueSmall = g_iconBlue;
            t.blueSmallOwned = false;
        }
    }
    if (!t.blueBig) return;
    SetWndIcon(t.wnd, ICON_BIG, t.blueBig);
    SetWndIcon(t.wnd, ICON_SMALL, t.blueSmall ? t.blueSmall : t.blueBig);
    t.iconBlue = true;
}

static void RefreshTargets(std::vector<Target>& ts) {
    std::vector<DWORD> pids = GetClientPids();
    for (size_t i = 0; i < ts.size();) {
        if (std::find(pids.begin(), pids.end(), ts[i].pid) == pids.end()) {
            FreeIcons(ts[i]);
            MarkLowered(ts[i].pid, false);
            CloseHandle(ts[i].h);
            ts.erase(ts.begin() + i);
        } else {
            ++i;
        }
    }
    for (size_t k = 0; k < pids.size(); ++k) {
        DWORD pid = pids[k];
        bool have = false;
        for (size_t i = 0; i < ts.size(); ++i) {
            if (ts[i].pid == pid) {
                ts[i].wnd = FindMainWindow(pid);
                have = true;
                break;
            }
        }
        if (have) continue;
        HANDLE h = OpenProcess(PROCESS_SUSPEND_RESUME | PROCESS_SET_INFORMATION | PROCESS_QUERY_INFORMATION | PROCESS_QUERY_LIMITED_INFORMATION, FALSE, pid);
        if (!h) h = OpenProcess(PROCESS_SUSPEND_RESUME | PROCESS_SET_INFORMATION | PROCESS_QUERY_LIMITED_INFORMATION, FALSE, pid);
        if (!h) h = OpenProcess(PROCESS_SUSPEND_RESUME | PROCESS_QUERY_LIMITED_INFORMATION, FALSE, pid);
        if (!h) continue;
        Target t;
        ZeroMemory(&t, sizeof(t));
        t.oldGpu = -1;
        t.oldIo = -1;
        t.pid = pid;
        t.h = h;
        t.wnd = FindMainWindow(pid);
        ts.push_back(t);
    }
}

static void BeginPeriod() {
    if (!g_hiRes && !g_periodOn) {
        timeBeginPeriod(1);
        g_periodOn = true;
    }
}

static void EndPeriod() {
    if (g_periodOn) {
        timeEndPeriod(1);
        g_periodOn = false;
    }
}

static void ReleaseTargets(std::vector<Target>& ts) {
    for (size_t i = 0; i < ts.size(); ++i) {
        ResumeT(ts[i]);
        RestoreClientIcon(ts[i]);
        FreeIcons(ts[i]);
        if (ts[i].lowered) {
            RestoreT(ts[i]);
            if (g_hWnd) PostMessageW(g_hWnd, WM_UI_REAPPLY, (WPARAM)ts[i].pid, 0);
        }
        CloseHandle(ts[i].h);
    }
    ts.clear();
}

static void EngineThread() {
    std::vector<Target> ts;
    ULONGLONG lastRefresh = 0;
    int lastUi = -1;
    while (g_run) {
        if (g_limitPause > 0) {
            // 調整視窗期間：先解除所有暫停，等調整完成後再恢復限制
            for (size_t i = 0; i < ts.size(); ++i) ResumeT(ts[i]);
            if (g_pauseAck) SetEvent(g_pauseAck);
            WaitForSingleObject(g_wake, 50);
            continue;
        }
        int mode = g_cpuEnabled ? (int)g_mode : 0;   // 總開關關閉時視同停用
        if (mode == 0) {
            // 停用：釋放所有行程狀態後完全休眠 (不輪詢、不佔 CPU)，直到設定改變或結束時被喚醒
            ReleaseTargets(ts);
            lastRefresh = 0;
            g_limitActive = false;
            EndPeriod();
            if (lastUi != 0) {
                lastUi = 0;
                if (g_hWnd) PostMessageW(g_hWnd, WM_UI_THROTTLE, 0, 0);
            }
            WaitForSingleObject(g_wake, INFINITE);
            continue;
        }
        ULONGLONG now = GetTickCount64();
        bool force = g_forceRefresh.exchange(false);   // 偵測到新的 Client 行程時立刻重新掃描
        if (force || lastRefresh == 0 || now - lastRefresh >= 3000) {
            RefreshTargets(ts);
            lastRefresh = now;
        }
        for (size_t i = 0; i < ts.size(); ++i) {
            if (!ts[i].wnd || !IsWindow(ts[i].wnd)) ts[i].wnd = FindMainWindow(ts[i].pid);   // 視窗晚一點才出現也能立刻接手
        }
        bool eco = g_eco;
        DWORD fgPid = 0;
        HWND fg = GetForegroundWindow();
        if (fg) GetWindowThreadProcessId(fg, &fgPid);

        std::vector<size_t> act;
        for (size_t i = 0; i < ts.size(); ++i) {
            Target& t = ts[i];
            bool want = false;
            // 還沒有視窗 (啟動/更新中) 的行程一律不限制，避免卡住啟動流程
            if (t.wnd && IsWindow(t.wnd)) {
                bool mini = IsIconic(t.wnd) != 0;
                if (mode == 1) want = true;
                else if (mode == 2) want = mini;
                else if (mode == 3) want = mini || (fgPid != t.pid);
            }
            if (!want) ResumeT(t);
            if (want != t.iconBlue) SetClientIconBlue(t, want);   // 此時行程未被暫停，可安全送出視窗訊息
            bool wantLow = want && eco;
            if (wantLow != t.lowered) {
                if (wantLow) {
                    LowerT(t);
                } else {
                    RestoreT(t);
                    if (g_hWnd) PostMessageW(g_hWnd, WM_UI_REAPPLY, (WPARAM)t.pid, 0);   // 解除限制後再套用一次設定值
                }
            } else if (wantLow) {
                EnforceLow(t);
            }
            if (want) act.push_back(i);
        }

        int ui = act.empty() ? 0 : 1;
        if (ui != lastUi) {
            lastUi = ui;
            if (g_hWnd) PostMessageW(g_hWnd, WM_UI_THROTTLE, (WPARAM)ui, 0);
        }
        if (act.empty()) {
            // 沒有需要限制的行程：前景 / 最小化變化由 WinEvent 即時喚醒，這裡只需低頻檢查新行程
            g_limitActive = false;
            EndPeriod();
            WaitForSingleObject(g_wake, 1000);
            continue;
        }

        g_limitActive = true;
        BeginPeriod();
        double suspendMs = 0, cycleMs = 0;
        CalcSlices(g_ratio, &suspendMs, &cycleMs);
        LARGE_INTEGER t0, t1;
        QueryPerformanceCounter(&t0);
        for (size_t i = 0; i < act.size(); ++i) SuspendT(ts[act[i]]);
        WaitMs(suspendMs);
        for (size_t i = 0; i < act.size(); ++i) ResumeT(ts[act[i]]);
        QueryPerformanceCounter(&t1);
        double elapsed = (double)(t1.QuadPart - t0.QuadPart) * 1000.0 / g_qpcFreq;
        double rest = cycleMs - elapsed;
        if (rest < 1.0) rest = 1.0;
        WaitMs(rest);
    }
    EndPeriod();
    ReleaseTargets(ts);
}

// 保險：解除所有 Client.exe 的暫停 (多呼叫幾次以清掉殘留的暫停計數)
static void ResumeAllClients() {
    if (!g_NtResume) return;
    std::vector<DWORD> pids = GetClientPids();
    for (size_t i = 0; i < pids.size(); ++i) {
        HANDLE h = OpenProcess(PROCESS_SUSPEND_RESUME, FALSE, pids[i]);
        if (h) {
            for (int k = 0; k < 3; ++k) g_NtResume(h);
            CloseHandle(h);
        }
    }
}

static void ShutdownEngine() {
    if (g_run.exchange(false)) {
        WakeEngine();
        if (g_engine.joinable()) g_engine.join();
    }
    ResumeAllClients();
}

static LONG WINAPI CrashFilter(EXCEPTION_POINTERS*) {
    ResumeAllClients();
    return EXCEPTION_CONTINUE_SEARCH;
}

// 鎖定位置：使用者開始拖曳 / 移動被鎖定的視窗時，立刻取消移動；結束後若位置有變就移回原位
static void OnMoveSize(bool start, HWND h) {
    if (!g_locked) return;
    std::map<HWND, POINT>::iterator it = g_lockPos.find(h);
    if (it == g_lockPos.end()) return;
    if (start) {
        PostMessageW(h, WM_KEYDOWN, VK_ESCAPE, 0x00010001);   // 等同在移動中按 Esc：取消移動
    } else {
        RECT r;
        GetWindowRect(h, &r);
        if (HasCaption(h) && (r.left != it->second.x || r.top != it->second.y))
            SetWindowPos(h, NULL, it->second.x, it->second.y, 0, 0, SWP_NOSIZE | SWP_NOZORDER | SWP_NOACTIVATE);
    }
}

// ---------------------------------------------------------------------------
//  模式還原 (事件驅動，不是輪詢)
//  遊戲自己改了視窗大小 / 位置 / 樣式之後 (例如遊戲裡「環境設定」按取消時，會把視窗還原成它記得的大小)，
//  依目前的模式還原，不會一直重設視窗：
//    * 無邊框模式：重新鋪滿所在螢幕的工作區
//    * 鎖定視窗大小 (一般視窗)：只把縮放邊框 / 最大化按鈕的樣式改回去，不動視窗的大小與位置
//  只在遊戲行程發出「視窗位置 / 大小改變」事件後才檢查 (等 0.25 秒沒有新變化才處理)；
//  遊戲反覆改回去時 5 秒內最多處理 6 次，避免和遊戲互相拉扯。
// ---------------------------------------------------------------------------
static HWINEVENTHOOK g_hookGame = NULL;
static DWORD g_hookGamePid = 0;
static ULONGLONG g_fixWindowStart = 0;
static int g_fixCount = 0;

static void ScheduleModeCheck() {
    if (g_hWnd && (g_borderless || g_locked)) SetTimer(g_hWnd, 5, 250, NULL);   // 重複設定 = 重新計時
}

static void ModeCheck() {
    if (!g_borderless && !g_locked) return;
    ULONGLONG now = GetTickCount64();
    if (now - g_fixWindowStart > 5000) {
        g_fixWindowStart = now;
        g_fixCount = 0;
    }
    if (g_fixCount >= 6) return;
    for (std::map<HWND, WinState>::iterator it = g_wins.begin(); it != g_wins.end(); ++it) {
        HWND h = it->first;
        if (!it->second.managed || !IsWindow(h) || IsIconic(h)) continue;
        if (g_borderless) {
            MONITORINFO mi;
            ZeroMemory(&mi, sizeof(mi));
            mi.cbSize = sizeof(mi);
            RECT r;
            if (!GetMonitorInfoW(MonitorFromWindow(h, MONITOR_DEFAULTTONEAREST), &mi) || !GetWindowRect(h, &r)) continue;
            if (HasCaption(h) || !EqualRect(&r, &mi.rcWork)) {
                LimitPause lp;
                ApplyBorderless(h);
                ++g_fixCount;
            }
        } else if (g_locked && HasCaption(h) && (GetWindowLongPtrW(h, GWL_STYLE) & WS_THICKFRAME)) {
            LimitPause lp;
            ApplyLock(h, true);
            ++g_fixCount;
        }
    }
}

static void CALLBACK WinEventProc(HWINEVENTHOOK, DWORD ev, HWND hwnd, LONG idObject, LONG, DWORD, DWORD) {
    if (ev == EVENT_OBJECT_LOCATIONCHANGE) {   // 只會收到遊戲行程的事件 (UpdateGameHook 以遊戲 PID 篩選)
        if (idObject == OBJID_WINDOW && hwnd && (hwnd == g_gameHwnd || g_wins.find(hwnd) != g_wins.end())) ScheduleModeCheck();
        return;
    }
    if (ev == EVENT_SYSTEM_MOVESIZESTART || ev == EVENT_SYSTEM_MOVESIZEEND) {
        if (idObject == OBJID_WINDOW && hwnd) OnMoveSize(ev == EVENT_SYSTEM_MOVESIZESTART, hwnd);
        return;
    }
    if (ev == EVENT_SYSTEM_MENUSTART || ev == EVENT_SYSTEM_MENUPOPUPSTART || ev == EVENT_SYSTEM_MENUEND) {
        // 系統每次開啟標題列選單時都會重設「移動」的狀態，所以一偵測到選單開啟就立刻再把它變灰
        if (ev != EVENT_SYSTEM_MENUEND && g_locked) {
            RegrayAllLocked();
            StartRegrayBurst();
        }
        return;
    }
    WakeEngine();
    UpdateOverlayVisibility();   // 前景 / 最小化改變：依「只在遊戲前景時顯示」更新疊加視窗
}

// 遊戲行程改變時，重新掛上「只監聽遊戲行程」的視窗位置 / 大小事件
static void UpdateGameHook() {
    DWORD pid = g_gamePid;
    if (pid == g_hookGamePid) return;
    if (g_hookGame) {
        UnhookWinEvent(g_hookGame);
        g_hookGame = NULL;
    }
    g_hookGamePid = pid;
    if (pid) g_hookGame = SetWinEventHook(EVENT_OBJECT_LOCATIONCHANGE, EVENT_OBJECT_LOCATIONCHANGE, NULL, WinEventProc, pid, 0, WINEVENT_OUTOFCONTEXT);
}

// ---------------------------------------------------------------------------
//  通知區域圖示
// ---------------------------------------------------------------------------
static HICON CreateBlueIcon(HICON src) {
    ICONINFO ii;
    if (!src || !GetIconInfo(src, &ii)) return src;
    BITMAP bm;
    ZeroMemory(&bm, sizeof(bm));
    if (!ii.hbmColor || !GetObjectW(ii.hbmColor, sizeof(bm), &bm) || bm.bmWidth <= 0 || bm.bmHeight <= 0) {
        if (ii.hbmColor) DeleteObject(ii.hbmColor);
        if (ii.hbmMask) DeleteObject(ii.hbmMask);
        return src;
    }
    int w = bm.bmWidth, h = bm.bmHeight;
    std::vector<DWORD> px((size_t)w * (size_t)h);
    BITMAPINFO bi;
    ZeroMemory(&bi, sizeof(bi));
    bi.bmiHeader.biSize = sizeof(BITMAPINFOHEADER);
    bi.bmiHeader.biWidth = w;
    bi.bmiHeader.biHeight = -h;
    bi.bmiHeader.biPlanes = 1;
    bi.bmiHeader.biBitCount = 32;
    bi.bmiHeader.biCompression = BI_RGB;
    HDC dc = GetDC(NULL);
    int got = GetDIBits(dc, ii.hbmColor, 0, (UINT)h, px.data(), &bi, DIB_RGB_COLORS);
    ReleaseDC(NULL, dc);
    HICON result = src;
    if (got) {
        bool hasAlpha = false;
        for (size_t i = 0; i < px.size(); ++i) {
            if ((px[i] >> 24) != 0) {
                hasAlpha = true;
                break;
            }
        }
        for (size_t i = 0; i < px.size(); ++i) {
            DWORD v = px[i];
            int a = (int)((v >> 24) & 0xFF), r = (int)((v >> 16) & 0xFF), g = (int)((v >> 8) & 0xFF), b = (int)(v & 0xFF);
            if (hasAlpha && a < 10) continue;
            if (r > 200 && g > 200 && b > 200) continue;
            if (r > b + 20) {
                int in = (r + g + b) / 3;
                int nr = std::min(255, in / 2 + 20);
                int ng = std::min(255, in + 40);
                px[i] = ((DWORD)a << 24) | ((DWORD)nr << 16) | ((DWORD)ng << 8) | 255u;
            }
        }
        HBITMAP nb = CreateBitmap(w, h, 1, 32, px.data());
        if (nb) {
            ICONINFO out = ii;
            out.hbmColor = nb;
            HICON ni = CreateIconIndirect(&out);
            if (ni) result = ni;
            DeleteObject(nb);
        }
    }
    DeleteObject(ii.hbmColor);
    DeleteObject(ii.hbmMask);
    return result;
}

// ===========================================================================
//  效能監控 (疊加視窗)：取樣執行緒 / FPS (ETW) / 繪製 / 選單
// ===========================================================================
struct OvSample {
    bool game;
    bool cpuOk, ghzOk, ramOk, gpuOk, vramOk, vramMbOk, fpsOk, latOk;
    double cpu, ghz, ramPct, ramMb, gpu, vramPct, vramMb, fps, lat;
};

// 等同 PROCESS_MEMORY_COUNTERS_EX2：PrivateWorkingSetSize 就是工作管理員「記憶體」欄位的「私有工作集」
struct PmcEx2 {
    DWORD cb;
    DWORD PageFaultCount;
    SIZE_T PeakWorkingSetSize;
    SIZE_T WorkingSetSize;
    SIZE_T QuotaPeakPagedPoolUsage;
    SIZE_T QuotaPagedPoolUsage;
    SIZE_T QuotaPeakNonPagedPoolUsage;
    SIZE_T QuotaNonPagedPoolUsage;
    SIZE_T PagefileUsage;
    SIZE_T PeakPagefileUsage;
    SIZE_T PrivateUsage;
    SIZE_T PrivateWorkingSetSize;
    ULONG64 SharedCommitUsage;
};

static std::mutex g_ovMtx;
static OvSample g_ovSample;
static std::thread g_monThread;
static std::atomic<bool> g_monRun(true);
static std::map<unsigned long long, unsigned long long> g_adapterVram;   // 顯示卡 LUID -> 專用顯示記憶體 (bytes)
static std::wstring g_ovLastSig;
static bool g_ovPosDirty = true;

static ULONGLONG FtToU64(const FILETIME& f) {
    return ((ULONGLONG)f.dwHighDateTime << 32) | (ULONGLONG)f.dwLowDateTime;
}

// ---------------------------------------------------------------------------
//  顯示卡專用顯示記憶體總量 (DXGI)
// ---------------------------------------------------------------------------
static void InitAdapterVram() {
    IDXGIFactory1* f = NULL;
    if (FAILED(CreateDXGIFactory1(__uuidof(IDXGIFactory1), (void**)&f)) || !f) return;
    for (UINT i = 0;; ++i) {
        IDXGIAdapter1* a = NULL;
        if (f->EnumAdapters1(i, &a) == DXGI_ERROR_NOT_FOUND) break;
        DXGI_ADAPTER_DESC1 d;
        if (SUCCEEDED(a->GetDesc1(&d))) {
            unsigned long long key = ((unsigned long long)(unsigned int)d.AdapterLuid.HighPart << 32) | (unsigned long long)d.AdapterLuid.LowPart;
            g_adapterVram[key] = (unsigned long long)d.DedicatedVideoMemory;
        }
        a->Release();
    }
    f->Release();
}

// ---------------------------------------------------------------------------
//  效能計數器 (PDH)：CPU 時脈 / GPU 使用率 / 專用顯示記憶體
// ---------------------------------------------------------------------------
struct PdhResult {
    bool sysOk;
    double sysUtil, sysTime;   // 診斷用：整體 CPU 的 % Processor Utility / % Processor Time
    bool ghzOk;
    double ghz;
    bool gpuOk;
    double gpu;
    bool vramOk;
    double vramBytes;
    bool luidOk;
    unsigned long long luid;
};

typedef std::vector<std::pair<std::wstring, double> > CounterArray;

static bool ReadCounterArray(PDH_HCOUNTER h, CounterArray& out) {
    DWORD size = 0, count = 0;
    PDH_STATUS st = PdhGetFormattedCounterArrayW(h, PDH_FMT_DOUBLE | PDH_FMT_NOCAP100, &size, &count, NULL);
    if (st == PDH_CSTATUS_NO_INSTANCE || st == PDH_NO_DATA) return true;   // 沒有任何符合的實例
    if (st != PDH_MORE_DATA) return false;
    std::vector<BYTE> buf(size);
    PDH_FMT_COUNTERVALUE_ITEM_W* items = (PDH_FMT_COUNTERVALUE_ITEM_W*)buf.data();
    st = PdhGetFormattedCounterArrayW(h, PDH_FMT_DOUBLE | PDH_FMT_NOCAP100, &size, &count, items);
    if (st != ERROR_SUCCESS) return false;
    for (DWORD i = 0; i < count; ++i) {
        DWORD cs = items[i].FmtValue.CStatus;
        if (cs == PDH_CSTATUS_VALID_DATA || cs == PDH_CSTATUS_NEW_DATA)
            out.push_back(std::make_pair(std::wstring(items[i].szName), items[i].FmtValue.doubleValue));
    }
    return true;
}

static bool ParseLuid(const std::wstring& name, unsigned long long* key) {
    size_t p = name.find(L"luid_0x");
    if (p == std::wstring::npos) return false;
    wchar_t* end = NULL;
    unsigned long hi = wcstoul(name.c_str() + p + 7, &end, 16);
    if (!end || wcsncmp(end, L"_0x", 3) != 0) return false;
    unsigned long lo = wcstoul(end + 3, NULL, 16);
    *key = ((unsigned long long)hi << 32) | (unsigned long long)lo;
    return true;
}

// 每次取樣建立一個新的查詢 (GPU 的計數器實例會隨行程變動)，連續收集兩次才能算出速率
static void PdhSampleAll(DWORD pid, unsigned long long aff, bool wantGhz, bool wantGpu, bool wantVram, bool wantSys, PdhResult& r) {
    ZeroMemory(&r, sizeof(r));
    PDH_HQUERY q = NULL;
    if (PdhOpenQueryW(NULL, 0, &q) != ERROR_SUCCESS) return;
    PDH_HCOUNTER hPerf = NULL, hFreq = NULL, hGpu = NULL, hMem = NULL, hSysU = NULL, hSysT = NULL;
    wchar_t path[256];
    if (wantSys) {   // 整體 CPU 的 Utility / Time (「估算」算法與診斷用)
        if (PdhAddEnglishCounterW(q, L"\\Processor Information(_Total)\\% Processor Utility", 0, &hSysU) != ERROR_SUCCESS) hSysU = NULL;
        if (PdhAddEnglishCounterW(q, L"\\Processor Information(_Total)\\% Processor Time", 0, &hSysT) != ERROR_SUCCESS) hSysT = NULL;
    }
    if (wantGhz) {
        if (PdhAddEnglishCounterW(q, L"\\Processor Information(*)\\% Processor Performance", 0, &hPerf) != ERROR_SUCCESS) hPerf = NULL;
        if (PdhAddEnglishCounterW(q, L"\\Processor Information(*)\\Processor Frequency", 0, &hFreq) != ERROR_SUCCESS) hFreq = NULL;
    }
    if (wantGpu) {
        wsprintfW(path, L"\\GPU Engine(pid_%lu_*)\\Utilization Percentage", (unsigned long)pid);
        if (PdhAddEnglishCounterW(q, path, 0, &hGpu) != ERROR_SUCCESS) hGpu = NULL;
    }
    if (wantVram) {
        wsprintfW(path, L"\\GPU Process Memory(pid_%lu_*)\\Dedicated Usage", (unsigned long)pid);
        if (PdhAddEnglishCounterW(q, path, 0, &hMem) != ERROR_SUCCESS) hMem = NULL;
    }
    PdhCollectQueryData(q);
    if (hPerf || hGpu || hSysU) {
        Sleep(200);
        PdhCollectQueryData(q);
    }
    if (hSysU || hSysT) {
        PDH_FMT_COUNTERVALUE fv2;
        DWORD ty2 = 0;
        bool suOk = false, stOk = false;
        if (hSysU && PdhGetFormattedCounterValue(hSysU, PDH_FMT_DOUBLE | PDH_FMT_NOCAP100, &ty2, &fv2) == ERROR_SUCCESS) {
            r.sysUtil = fv2.doubleValue;
            suOk = true;
        }
        if (hSysT && PdhGetFormattedCounterValue(hSysT, PDH_FMT_DOUBLE | PDH_FMT_NOCAP100, &ty2, &fv2) == ERROR_SUCCESS) {
            r.sysTime = fv2.doubleValue;
            stOk = true;
        }
        r.sysOk = suOk && stOk;
    }
    if (hPerf && hFreq) {
        CounterArray perf, freq;
        if (ReadCounterArray(hPerf, perf) && ReadCounterArray(hFreq, freq)) {
            std::map<std::wstring, double> fm(freq.begin(), freq.end());
            double sum = 0;
            int n = 0;
            for (size_t i = 0; i < perf.size(); ++i) {
                const std::wstring& nm = perf[i].first;
                size_t comma = nm.find(L',');
                if (comma == std::wstring::npos || nm.find(L'_') != std::wstring::npos) continue;   // 略過 _Total
                int idx = _wtoi(nm.c_str() + comma + 1);
                if (idx < 0 || idx >= 64 || !((aff >> idx) & 1)) continue;   // 只算遊戲可使用的核心
                std::map<std::wstring, double>::iterator it = fm.find(nm);
                if (it == fm.end()) continue;
                sum += it->second * perf[i].second / 100.0;   // 額定頻率 (MHz) x 效能百分比
                ++n;
            }
            if (n) {
                r.ghz = sum / n / 1000.0;
                r.ghzOk = true;
            }
        }
    }
    if (hGpu) {
        CounterArray a;
        if (ReadCounterArray(hGpu, a)) {
            double mx = 0;   // 同工作管理員：取各引擎中最高的
            for (size_t i = 0; i < a.size(); ++i) mx = std::max(mx, a[i].second);
            r.gpu = mx;
            r.gpuOk = true;
        }
    }
    if (hMem) {
        CounterArray a;
        if (ReadCounterArray(hMem, a)) {
            double best = 0;
            for (size_t i = 0; i < a.size(); ++i) {
                if (a[i].second >= best) {
                    best = a[i].second;
                    r.luidOk = ParseLuid(a[i].first, &r.luid);
                }
            }
            r.vramBytes = best;
            r.vramOk = true;
        }
    }
    PdhCloseQuery(q);
}

// ---------------------------------------------------------------------------
//  FPS：ETW (事件追蹤) 監聽 Present 事件，與 PresentMon 相同的來源
//  目前支援：Direct3D 9 (Microsoft-Windows-D3D9) 與 DXGI (Direct3D 10 / 11 / 12)
//  預留：DXVK (Vulkan) 需要再加入 DxgKrnl 的呈現事件，等實際換成 DXVK 時在你的機器上驗證後補上
// ---------------------------------------------------------------------------
static const GUID kGuidD3D9 = { 0x783ACA0A, 0x790E, 0x4D7F, { 0x84, 0x51, 0xAA, 0x85, 0x05, 0x11, 0xC6, 0xB9 } };
static const GUID kGuidDXGI = { 0xCA11C036, 0x0102, 0x4A2D, { 0xA6, 0xAD, 0xF0, 0x3C, 0xFE, 0xD5, 0xD3, 0xC9 } };
static const wchar_t kEtwName[] = L"ClientManagerFpsSession";
static TRACEHANDLE g_etwSession = 0;
static std::thread g_etwThread;
static std::atomic<unsigned long long> g_fpsD3d9(0);
static std::atomic<unsigned long long> g_fpsDxgi(0);
static std::mutex g_etwDbgMtx;
static std::map<unsigned long long, unsigned long long> g_etwSeen;   // 診斷用：(提供者 << 32 | 事件編號) -> 次數

static void WINAPI EtwCallback(PEVENT_RECORD r) {
    if (r->EventHeader.ProcessId != g_fpsPid) return;
    USHORT id = r->EventHeader.EventDescriptor.Id;
    int prov = 0;
    if (IsEqualGUID(r->EventHeader.ProviderId, kGuidD3D9)) {
        prov = 1;
        if (id == 1) g_fpsD3d9++;    // D3D9 Present 開始
    } else if (IsEqualGUID(r->EventHeader.ProviderId, kGuidDXGI)) {
        prov = 2;
        if (id == 42) g_fpsDxgi++;   // DXGI Present 開始
    }
    if (g_ovDebug && prov) {
        std::lock_guard<std::mutex> lk(g_etwDbgMtx);
        g_etwSeen[((unsigned long long)prov << 32) | (unsigned long long)id]++;
    }
}

static void FillTraceProps(std::vector<BYTE>& buf) {
    ZeroMemory(buf.data(), buf.size());
    EVENT_TRACE_PROPERTIES* p = (EVENT_TRACE_PROPERTIES*)buf.data();
    p->Wnode.BufferSize = (ULONG)buf.size();
    p->Wnode.Flags = WNODE_FLAG_TRACED_GUID;
    p->Wnode.ClientContext = 1;   // 使用 QPC 時間戳
    p->LogFileMode = EVENT_TRACE_REAL_TIME_MODE;
    p->LoggerNameOffset = sizeof(EVENT_TRACE_PROPERTIES);
}

static bool StartFps() {
    if (g_etwThread.joinable()) return true;
    std::vector<BYTE> buf(sizeof(EVENT_TRACE_PROPERTIES) + sizeof(kEtwName));
    FillTraceProps(buf);
    ULONG st = StartTraceW(&g_etwSession, kEtwName, (EVENT_TRACE_PROPERTIES*)buf.data());
    if (st == ERROR_ALREADY_EXISTS) {   // 上次異常結束留下的 session：先停掉再重建
        FillTraceProps(buf);
        ControlTraceW(0, kEtwName, (EVENT_TRACE_PROPERTIES*)buf.data(), EVENT_TRACE_CONTROL_STOP);
        FillTraceProps(buf);
        st = StartTraceW(&g_etwSession, kEtwName, (EVENT_TRACE_PROPERTIES*)buf.data());
    }
    if (st != ERROR_SUCCESS) {
        g_etwSession = 0;
        return false;
    }
    EnableTraceEx2(g_etwSession, &kGuidD3D9, EVENT_CONTROL_CODE_ENABLE_PROVIDER, TRACE_LEVEL_INFORMATION, 0xFFFFFFFFFFFFFFFFULL, 0, 0, NULL);
    EnableTraceEx2(g_etwSession, &kGuidDXGI, EVENT_CONTROL_CODE_ENABLE_PROVIDER, TRACE_LEVEL_INFORMATION, 0xFFFFFFFFFFFFFFFFULL, 0, 0, NULL);
    g_etwThread = std::thread([]() {
        EVENT_TRACE_LOGFILEW lf;
        ZeroMemory(&lf, sizeof(lf));
        lf.LoggerName = (LPWSTR)kEtwName;
        lf.ProcessTraceMode = PROCESS_TRACE_MODE_REAL_TIME | PROCESS_TRACE_MODE_EVENT_RECORD | PROCESS_TRACE_MODE_RAW_TIMESTAMP;
        lf.EventRecordCallback = EtwCallback;
        TRACEHANDLE h = OpenTraceW(&lf);
        if (h == INVALID_PROCESSTRACE_HANDLE) return;
        ProcessTrace(&h, 1, NULL, NULL);
        CloseTrace(h);
    });
    return true;
}

static void StopFps() {
    if (g_etwSession) {
        std::vector<BYTE> buf(sizeof(EVENT_TRACE_PROPERTIES) + sizeof(kEtwName));
        FillTraceProps(buf);
        ControlTraceW(g_etwSession, kEtwName, (EVENT_TRACE_PROPERTIES*)buf.data(), EVENT_TRACE_CONTROL_STOP);
        g_etwSession = 0;
    }
    if (g_etwThread.joinable()) g_etwThread.join();
}

static void UpdateFpsSession() {
    if (g_ovEnabled && g_ovFps) StartFps();
    else StopFps();
}

// 診斷：在監控設定視窗勾選「診斷記錄」時統計收到的事件，顯示在視窗的記錄區塊 (不寫入檔案)，用來確認 FPS 的事件編號
static std::mutex g_dbgMtx;
static std::string g_cpuDbg;   // CPU / PDH 診斷 (監控執行緒寫入，設定視窗讀取)
static std::string g_latDbg;   // 網路延遲診斷

// 目前的診斷記錄 (不寫入檔案，只顯示在監控設定視窗，可按「複製」)
static std::wstring BuildDebugText() {
    std::string out;
    {
        std::lock_guard<std::mutex> lk(g_dbgMtx);
        out += g_cpuDbg;
        out += g_latDbg;
    }
    {
        std::lock_guard<std::mutex> lk(g_etwDbgMtx);
        if (!g_etwSeen.empty()) out += "fps: ETW events seen\r\n";
        for (std::map<unsigned long long, unsigned long long>::iterator it = g_etwSeen.begin(); it != g_etwSeen.end(); ++it) {
            char b[128];
            snprintf(b, sizeof(b), "  provider=%s eventId=%u count=%llu\r\n", (it->first >> 32) == 1 ? "D3D9" : "DXGI",
                     (unsigned)(it->first & 0xFFFFFFFF), it->second);
            out += b;
        }
    }
    if (out.empty()) return L"(no data yet - enable the monitor and run the game)\r\n";
    std::wstring w;
    for (size_t i = 0; i < out.size(); ++i) w += (wchar_t)(unsigned char)out[i];
    return w;
}

// ---------------------------------------------------------------------------
//  取樣執行緒：只取樣「有勾選」的項目；沒有啟用監控或遊戲沒開時完全休眠
// ---------------------------------------------------------------------------
// ---------------------------------------------------------------------------
//  CPU 週期數 (週期法)：使用率 = 行程的 CPU 週期增量 / (經過時間 x 邏輯核心數 x CPU 額定頻率)
// ---------------------------------------------------------------------------
typedef BOOL (WINAPI* pfnQueryProcessCycleTime)(HANDLE, PULONG64);

static DWORD ReadNominalMhz() {
    DWORD v = 0, sz = sizeof(v);
    if (RegGetValueW(HKEY_LOCAL_MACHINE, L"HARDWARE\\DESCRIPTION\\System\\CentralProcessor\\0", L"~MHz", RRF_RT_REG_DWORD, NULL, &v, &sz) == ERROR_SUCCESS) return v;
    return 0;
}

// ---------------------------------------------------------------------------
//  網路延遲：同資源監視器「TCP 連線」的延遲 (TCP 延伸統計的平滑往返時間)
//  只看遊戲行程的連線，排除連接埠 80 / 443 與聊天伺服器 (chatip / chatport)；
//  已登入分流後取連接埠 >= 11000 的連線，登入畫面 (尚未分流) 則使用啟動參數的 logip / logport
// ---------------------------------------------------------------------------
static std::set<unsigned long long> g_estatsOn;   // 監控執行緒專用：已開啟延伸統計的連線

static std::wstring ArgValue(const std::wstring& args, const std::wstring& key) {
    size_t pos = 0;
    while ((pos = args.find(key, pos)) != std::wstring::npos) {
        if (pos == 0 || args[pos - 1] == L' ') {
            size_t b = pos + key.size();
            size_t e = args.find(L' ', b);
            return args.substr(b, e == std::wstring::npos ? std::wstring::npos : e - b);
        }
        pos += key.size();
    }
    return L"";
}

static DWORD ParseIpv4(const std::wstring& s) {
    unsigned part[4] = { 0, 0, 0, 0 };
    int idx = 0;
    bool any = false;
    for (size_t i = 0; i < s.size(); ++i) {
        wchar_t c = s[i];
        if (c >= L'0' && c <= L'9') {
            part[idx] = part[idx] * 10 + (unsigned)(c - L'0');
            any = true;
            if (part[idx] > 255) return 0;
        } else if (c == L'.' && any && idx < 3) {
            ++idx;
            any = false;
        } else {
            return 0;
        }
    }
    if (idx != 3 || !any) return 0;
    return part[0] | (part[1] << 8) | (part[2] << 16) | (part[3] << 24);   // 與 TCP 表一致 (網路位元組順序)
}

struct TcpCand {
    MIB_TCPROW row;
    int rport;
    int tag;   // 0 = 其他、1 = 網頁 (80 / 443)、2 = 聊天、3 = 登入、4 = 遊戲 (連接埠 >= 11000)
};

static bool ReadTcpRtt(MIB_TCPROW row, TCP_ESTATS_PATH_ROD_v0* rod) {
    unsigned long long key = ((unsigned long long)row.dwRemoteAddr << 32) | ((unsigned long long)(row.dwRemotePort & 0xFFFF) << 16) | (unsigned long long)(row.dwLocalPort & 0xFFFF);
    if (g_estatsOn.find(key) == g_estatsOn.end()) {
        TCP_ESTATS_PATH_RW_v0 rw;
        rw.EnableCollection = TRUE;
        if (SetPerTcpConnectionEStats(&row, TcpConnectionEstatsPath, (PUCHAR)&rw, 0, sizeof(rw), 0) != NO_ERROR) return false;
        g_estatsOn.insert(key);
    }
    ZeroMemory(rod, sizeof(*rod));
    return GetPerTcpConnectionEStats(&row, TcpConnectionEstatsPath, NULL, 0, 0, NULL, 0, 0, (PUCHAR)rod, 0, sizeof(*rod)) == NO_ERROR;
}

static bool SampleLatency(DWORD pid, const std::wstring& args, DWORD* outMs, std::string* dbg) {
    ULONG size = 0;
    GetExtendedTcpTable(NULL, &size, FALSE, AF_INET, TCP_TABLE_OWNER_PID_ALL, 0);
    if (size == 0) return false;
    std::vector<BYTE> buf(size + 1024);
    ULONG sz2 = (ULONG)buf.size();
    PMIB_TCPTABLE_OWNER_PID tbl = (PMIB_TCPTABLE_OWNER_PID)buf.data();
    if (GetExtendedTcpTable(tbl, &sz2, FALSE, AF_INET, TCP_TABLE_OWNER_PID_ALL, 0) != NO_ERROR) return false;
    DWORD chatIp = ParseIpv4(ArgValue(args, L"chatip:"));
    int chatPort = _wtoi(ArgValue(args, L"chatport:").c_str());
    DWORD logIp = ParseIpv4(ArgValue(args, L"logip:"));
    int logPort = _wtoi(ArgValue(args, L"logport:").c_str());
    std::vector<TcpCand> cands;
    for (DWORD i = 0; i < tbl->dwNumEntries; ++i) {
        const MIB_TCPROW_OWNER_PID& r = tbl->table[i];
        if (r.dwOwningPid != pid || r.dwState != MIB_TCP_STATE_ESTAB) continue;
        TcpCand c;
        ZeroMemory(&c, sizeof(c));
        c.row.dwState = r.dwState;
        c.row.dwLocalAddr = r.dwLocalAddr;
        c.row.dwLocalPort = r.dwLocalPort;
        c.row.dwRemoteAddr = r.dwRemoteAddr;
        c.row.dwRemotePort = r.dwRemotePort;
        c.rport = (int)(((r.dwRemotePort & 0xFF) << 8) | ((r.dwRemotePort >> 8) & 0xFF));
        if (c.rport == 80 || c.rport == 443) c.tag = 1;
        else if (chatPort && c.rport == chatPort && r.dwRemoteAddr == chatIp) c.tag = 2;
        else if (logPort && c.rport == logPort && r.dwRemoteAddr == logIp) c.tag = 3;
        else if (c.rport >= 11000) c.tag = 4;
        else c.tag = 0;
        cands.push_back(c);
    }
    int pick = -1;   // 已分流：第一條連接埠 >= 11000 的連線；登入畫面：登入伺服器的連線
    for (size_t i = 0; i < cands.size() && pick < 0; ++i) if (cands[i].tag == 4) pick = (int)i;
    for (size_t i = 0; i < cands.size() && pick < 0; ++i) if (cands[i].tag == 3) pick = (int)i;
    bool ok = false;
    if (pick >= 0) {
        TCP_ESTATS_PATH_ROD_v0 rod;
        if (ReadTcpRtt(cands[pick].row, &rod) && rod.CountRtt != 0) {   // CountRtt = 0：還沒有量到往返時間
            // 取樣方式 (OvLatencyMethod)：0 = 最近一次樣本值 (預設)，1 = 平滑往返時間；另一個值為 0 時互相替代
            DWORD v = (g_ovLatMethod == 1) ? rod.SmoothedRtt : rod.SampleRtt;
            if (v == 0) v = (g_ovLatMethod == 1) ? rod.SampleRtt : rod.SmoothedRtt;
            *outMs = v;
            ok = true;
        }
    }
    if (dbg) {   // 診斷：列出遊戲行程的所有連線與各自的往返時間
        static const char* const kTag[5] = { "other", "web", "chat", "login", "game" };
        std::string out = std::string("latency: ESTABLISHED connections of the game process (shown value of the picked one = ") +
                          (g_ovLatMethod == 1 ? "smoothed RTT" : "latest sample") + ")\r\n";
        char b[256];
        snprintf(b, sizeof(b), "  args: chat=%lu.%lu.%lu.%lu:%d login=%lu.%lu.%lu.%lu:%d\r\n",
                 (unsigned long)(chatIp & 255), (unsigned long)((chatIp >> 8) & 255), (unsigned long)((chatIp >> 16) & 255), (unsigned long)((chatIp >> 24) & 255), chatPort,
                 (unsigned long)(logIp & 255), (unsigned long)((logIp >> 8) & 255), (unsigned long)((logIp >> 16) & 255), (unsigned long)((logIp >> 24) & 255), logPort);
        out += b;
        for (size_t i = 0; i < cands.size(); ++i) {
            const TcpCand& c = cands[i];
            DWORD a = c.row.dwRemoteAddr;
            TCP_ESTATS_PATH_ROD_v0 rod;
            bool have = ReadTcpRtt(c.row, &rod);
            if (have) {
                snprintf(b, sizeof(b), "  %s%lu.%lu.%lu.%lu:%d [%s] smoothed=%lu sample=%lu min=%lu max=%lu count=%lu\r\n", (int)i == pick ? "-> " : "   ",
                         (unsigned long)(a & 255), (unsigned long)((a >> 8) & 255), (unsigned long)((a >> 16) & 255), (unsigned long)((a >> 24) & 255),
                         c.rport, kTag[c.tag], (unsigned long)rod.SmoothedRtt, (unsigned long)rod.SampleRtt, (unsigned long)rod.MinRtt, (unsigned long)rod.MaxRtt, (unsigned long)rod.CountRtt);
            } else {
                snprintf(b, sizeof(b), "  %s%lu.%lu.%lu.%lu:%d [%s] (no RTT statistics)\r\n", (int)i == pick ? "-> " : "   ",
                         (unsigned long)(a & 255), (unsigned long)((a >> 8) & 255), (unsigned long)((a >> 16) & 255), (unsigned long)((a >> 24) & 255), c.rport, kTag[c.tag]);
            }
            out += b;
        }
        if (cands.empty()) out += "  (no connections)\r\n";
        *dbg = out;
    }
    return ok;
}

static void PostOverlaySample(const OvSample& s) {
    {
        std::lock_guard<std::mutex> lk(g_ovMtx);
        g_ovSample = s;
    }
    if (g_hWnd) PostMessageW(g_hWnd, WM_UI_OVERLAY, 0, 0);
}

static void MonitorThread() {
    DWORD curPid = 0;
    HANDLE hProc = NULL;
    ULONGLONG lastProc = 0, lastWall = 0;
    bool cpuPrimed = false;
    ULONG64 lastCyc = 0;
    ULONGLONG lastWallC = 0;
    bool cycPrimed = false;
    pfnQueryProcessCycleTime fnCycle = (pfnQueryProcessCycleTime)GetProcAddress(GetModuleHandleW(L"kernel32.dll"), "QueryProcessCycleTime");
    DWORD nominalMhz = ReadNominalMhz();
    unsigned long long lastD3d9 = 0, lastDxgi = 0;
    ULONGLONG lastFpsTick = 0;
    bool fpsSeen = false;
    bool lastFpsOk = false;
    double lastFps = 0;
    bool adaptersInit = false;
    bool lastWasNone = false;
    OvSample none;
    ZeroMemory(&none, sizeof(none));
    while (g_monRun) {
        DWORD pid = g_gamePid;
        if ((!g_ovEnabled && !g_ovDebug) || pid == 0) {
            if (hProc) {
                CloseHandle(hProc);
                hProc = NULL;
            }
            curPid = 0;
            if (!lastWasNone) {
                PostOverlaySample(none);
                lastWasNone = true;
            }
            WaitForSingleObject(g_monWake, INFINITE);
            continue;
        }
        lastWasNone = false;
        if (pid != curPid) {
            if (hProc) CloseHandle(hProc);
            hProc = OpenProcess(PROCESS_QUERY_INFORMATION | PROCESS_VM_READ, FALSE, pid);
            if (!hProc) hProc = OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION, FALSE, pid);
            curPid = pid;
            cpuPrimed = false;
            cycPrimed = false;
            g_estatsOn.clear();
            lastD3d9 = lastDxgi = 0;
            g_fpsD3d9 = 0;
            g_fpsDxgi = 0;
            fpsSeen = false;
            lastFpsOk = false;
            lastFpsTick = GetTickCount64();
        }
        ULONGLONG t0 = GetTickCount64();
        OvSample s;
        ZeroMemory(&s, sizeof(s));
        s.game = true;

        // CPU 使用率 (以全部邏輯核心為 100%)。算法 (ini 的 OvCpuMethod)：
        //   0 = 週期法 (預設)：行程 CPU 週期數增量 / (經過時間 x 邏輯核心數 x CPU 額定頻率)
        //   1 = 時間法：行程 CPU 時間增量 / (經過時間 x 邏輯核心數)
        //   2 = 估算：時間法 x (整體 % Processor Utility / 整體 % Processor Time)
        // 每種算法都量測，某種算法取不到資料時才有資料可以退回
        DWORD ncpuAll = GetActiveProcessorCount(ALL_PROCESSOR_GROUPS);
        if (ncpuAll == 0) ncpuAll = 1;
        bool cycOk = false, timeOk = false, pdhSysOk = false;
        double cycPct = 0, timePct = 0, pdhSysU = 0, pdhSysT = 0;
        if (hProc && (g_ovCpu || g_ovDebug)) {
            FILETIME nowFt;
            GetSystemTimeAsFileTime(&nowFt);
            ULONGLONG wall = FtToU64(nowFt);
            ULONG64 cyc = 0;
            if (fnCycle && nominalMhz > 0 && fnCycle(hProc, &cyc)) {
                if (cycPrimed && wall > lastWallC) {
                    double dt = (double)(wall - lastWallC) / 1.0e7;
                    double capacity = dt * (double)ncpuAll * (double)nominalMhz * 1.0e6;
                    cycPct = (double)(cyc - lastCyc) * 100.0 / capacity;
                    cycOk = true;
                }
                lastCyc = cyc;
                lastWallC = wall;
                cycPrimed = true;
            }
            FILETIME c, e, k, u;
            if (GetProcessTimes(hProc, &c, &e, &k, &u)) {
                ULONGLONG proc = FtToU64(k) + FtToU64(u);
                if (cpuPrimed && wall > lastWall) {
                    timePct = (double)(proc - lastProc) * 100.0 / ((double)(wall - lastWall) * (double)ncpuAll);
                    timeOk = true;
                }
                lastProc = proc;
                lastWall = wall;
                cpuPrimed = true;
            }
        }

        // RAM：私有工作集，與工作管理員相同；比例以全部實體記憶體為基準
        if (hProc && g_ovRam) {
            PmcEx2 pm;
            ZeroMemory(&pm, sizeof(pm));
            pm.cb = sizeof(pm);
            MEMORYSTATUSEX ms;
            ZeroMemory(&ms, sizeof(ms));
            ms.dwLength = sizeof(ms);
            if (GetProcessMemoryInfo(hProc, (PROCESS_MEMORY_COUNTERS*)&pm, sizeof(pm)) && pm.PrivateWorkingSetSize > 0 &&
                GlobalMemoryStatusEx(&ms) && ms.ullTotalPhys > 0) {
                s.ramMb = (double)pm.PrivateWorkingSetSize / 1048576.0;
                s.ramPct = (double)pm.PrivateWorkingSetSize * 100.0 / (double)ms.ullTotalPhys;
                s.ramOk = true;
            }
        }

        // CPU 時脈 / GPU 使用率 / 專用顯示記憶體：效能計數器
        bool wantGhz = g_ovCpu && g_ovCpuGhz;
        bool wantGpu = g_ovGpu;
        bool wantVram = g_ovVram;
        bool wantSysPdh = (g_ovCpu && g_ovCpuMethod == 2) || g_ovDebug;   // 估算算法與診斷用
        if (wantGhz || wantGpu || wantVram || wantSysPdh) {
            if (wantVram && !adaptersInit) {
                InitAdapterVram();
                adaptersInit = true;
            }
            unsigned long long aff = (unsigned long long)g_maskAll;
            DWORD_PTR pm = 0, sm = 0;
            if (hProc && GetProcessAffinityMask(hProc, &pm, &sm) && pm) aff = (unsigned long long)pm;
            PdhResult r;
            PdhSampleAll(pid, aff, wantGhz, wantGpu, wantVram, wantSysPdh, r);
            pdhSysOk = r.sysOk;
            pdhSysU = r.sysUtil;
            pdhSysT = r.sysTime;
            s.ghzOk = r.ghzOk;
            s.ghz = r.ghz;
            s.gpuOk = r.gpuOk;
            s.gpu = r.gpu;
            if (r.vramOk) {
                s.vramMb = r.vramBytes / 1048576.0;
                s.vramMbOk = true;
                if (r.luidOk) {
                    std::map<unsigned long long, unsigned long long>::iterator it = g_adapterVram.find(r.luid);
                    if (it != g_adapterVram.end() && it->second >= (256ULL << 20)) {   // 內顯沒有專用顯示記憶體：比例顯示 --
                        s.vramPct = r.vramBytes * 100.0 / (double)it->second;
                        s.vramOk = true;
                    }
                }
            }
        }

        if (g_ovDebug) {
            char b[512];
            snprintf(b, sizeof(b), "cpu: method=%d  cycles=%s %.2f%%  time=%s %.2f%%  nominalMHz=%lu logicalCPUs=%lu\r\n",
                     (int)g_ovCpuMethod, cycOk ? "ok" : "n/a", cycPct, timeOk ? "ok" : "n/a", timePct,
                     (unsigned long)nominalMhz, (unsigned long)ncpuAll);
            std::string line = b;
            snprintf(b, sizeof(b), "cpu: system(_Total) utility=%s%.2f%% time=%s%.2f%%\r\n", pdhSysOk ? "" : "n/a ", pdhSysU, pdhSysOk ? "" : "n/a ", pdhSysT);
            line += b;
            if (pdhSysOk && pdhSysT > 0.0 && timeOk) {
                snprintf(b, sizeof(b), "cpu: estimate = process time%% x system utility / system time = %.2f%%\r\n", timePct * pdhSysU / pdhSysT);
                line += b;
            }
            std::lock_guard<std::mutex> lk(g_dbgMtx);
            g_cpuDbg = line;
        }

        // 依選定的算法採用 CPU 使用率 (取不到時依序退回：週期法 -> 時間法)
        if (g_ovCpu) {
            int method = g_ovCpuMethod;
            bool done = false;
            double v = 0;
            if (method == 2 && pdhSysOk && timeOk) {   // 估算：行程時間 x (系統 Utility / 系統 Time)
                double ratio = (pdhSysT > 0.5) ? pdhSysU / pdhSysT : 1.0;
                v = timePct * std::max(0.2, std::min(5.0, ratio));
                done = true;
            }
            if (!done && method != 1 && cycOk) { v = cycPct; done = true; }
            if (!done && timeOk) { v = timePct; done = true; }
            if (done) {
                s.cpu = std::max(0.0, std::min(100.0, v));
                s.cpuOk = true;
            }
        }

        // FPS：兩次取樣之間收到的 Present 事件數 / 經過時間
        if (g_ovFps) {
            ULONGLONG now = GetTickCount64();
            unsigned long long d9 = g_fpsD3d9, dx = g_fpsDxgi;
            double dt = (double)(now - lastFpsTick) / 1000.0;
            if (dt >= 0.2) {
                unsigned long long n9 = d9 - lastD3d9, nx = dx - lastDxgi;
                unsigned long long n = n9 ? n9 : nx;
                if (n) fpsSeen = true;
                if (fpsSeen) {
                    lastFps = (double)n / dt;
                    lastFpsOk = true;
                }
                lastD3d9 = d9;
                lastDxgi = dx;
                lastFpsTick = now;
            }
            s.fps = lastFps;
            s.fpsOk = lastFpsOk;
        }

        // 網路延遲：只在顯示該項目時才查詢連線表
        if (g_ovLatency || g_ovDebug) {
            DWORD ms = 0;
            std::string latDbg;
            if (SampleLatency(pid, GetCachedArgs(), &ms, g_ovDebug ? &latDbg : NULL)) {
                s.lat = (double)ms;
                s.latOk = true;
            }
            if (g_ovDebug) {
                std::lock_guard<std::mutex> lk(g_dbgMtx);
                g_latDbg = latDbg.empty() ? std::string("latency: (no data)\r\n") : latDbg;
            }
        }

        PostOverlaySample(s);

        ULONGLONG el = GetTickCount64() - t0;
        ULONGLONG iv = (ULONGLONG)(int)g_ovIntervalMs;
        DWORD wait = (el >= iv) ? 50 : (DWORD)(iv - el);
        WaitForSingleObject(g_monWake, wait);
    }
    if (hProc) CloseHandle(hProc);
}

// ---------------------------------------------------------------------------
//  顯示文字
// ---------------------------------------------------------------------------
static std::wstring Thousands(unsigned long v) {
    wchar_t b[32];
    wsprintfW(b, L"%lu", v);
    std::wstring s = b, r;
    int n = (int)s.size();
    for (int i = 0; i < n; ++i) {
        r += s[i];
        int rem = n - 1 - i;
        if (rem > 0 && rem % 3 == 0) r += L',';
    }
    return r;
}

static std::wstring FmtPct(double v) {
    int tenths = (int)(v * 10.0 + 0.5);   // 以 0.1% 為單位四捨五入
    wchar_t b[32];
    if (tenths % 10 == 0) wsprintfW(b, L"%d%%", tenths / 10);              // 整數：不顯示小數
    else wsprintfW(b, L"%d.%d%%", tenths / 10, tenths % 10);               // 非整數：顯示到小數第一位
    return b;
}

static std::wstring FmtGhz(double g) {
    int h = (int)(g * 100.0 + 0.5);
    wchar_t b[32];
    wsprintfW(b, L"%d.%02d GHz", h / 100, h % 100);
    return b;
}

static std::wstring FmtMb(double mb) {
    return Thousands((unsigned long)(mb + 0.5)) + L" MB";
}

static bool HasAnyOverlayItem() {
    return (g_ovCpu && (g_ovCpuPct || g_ovCpuGhz)) || (g_ovRam && (g_ovRamPct || g_ovRamMb)) || g_ovGpu ||
           (g_ovVram && (g_ovVramPct || g_ovVramMb)) || g_ovFps || g_ovLatency;
}

// 順序：CPU (限制中時在後面加註)、RAM、GPU、VRAM、FPS；標籤固定為英文
static void BuildOverlayLines(const OvSample& s, std::vector<std::wstring>& lines) {
    const std::wstring none = L"--";
    std::wstring txt[OVI_COUNT];
    if (g_ovCpu && (g_ovCpuPct || g_ovCpuGhz)) {
        std::wstring v;
        if (g_ovCpuPct) v += s.cpuOk ? FmtPct(s.cpu) : none;
        if (g_ovCpuPct && g_ovCpuGhz) v += L" / ";
        if (g_ovCpuGhz) v += s.ghzOk ? FmtGhz(s.ghz) : none;
        std::wstring it = L"CPU: " + v;
        if (g_throttleOn) it += L" " + std::wstring(T(S_OV_LIMITING));
        txt[OVI_CPU] = it;
    }
    if (g_ovRam && (g_ovRamPct || g_ovRamMb)) {
        std::wstring v;
        if (g_ovRamPct) v += s.ramOk ? FmtPct(s.ramPct) : none;
        if (g_ovRamPct && g_ovRamMb) v += L" / ";
        if (g_ovRamMb) v += s.ramOk ? FmtMb(s.ramMb) : none;
        txt[OVI_RAM] = L"RAM: " + v;
    }
    if (g_ovGpu) txt[OVI_GPU] = L"GPU: " + (s.gpuOk ? FmtPct(s.gpu) : none);
    if (g_ovVram && (g_ovVramPct || g_ovVramMb)) {
        std::wstring v;
        if (g_ovVramPct) v += s.vramOk ? FmtPct(s.vramPct) : none;
        if (g_ovVramPct && g_ovVramMb) v += L" / ";
        if (g_ovVramMb) v += s.vramMbOk ? FmtMb(s.vramMb) : none;
        txt[OVI_VRAM] = L"VRAM: " + v;
    }
    if (g_ovFps) {
        wchar_t b[32];
        wsprintfW(b, L"%d", (int)(s.fps + 0.5));
        txt[OVI_FPS] = L"FPS: " + (s.fpsOk ? std::wstring(b) : none);
    }
    if (g_ovLatency) {
        wchar_t b[32];
        wsprintfW(b, L"%lu ms", (unsigned long)(s.lat + 0.5));
        txt[OVI_LAT] = L"Latency: " + (s.latOk ? std::wstring(b) : none);
    }
    std::vector<std::wstring> items;
    for (size_t k = 0; k < g_ovOrder.size(); ++k) {   // 依設定的順序排列
        int id = g_ovOrder[k];
        if (id >= 0 && id < OVI_COUNT && !txt[id].empty()) items.push_back(txt[id]);
    }
    if (items.empty()) return;
    if (g_ovLayout == 1) {
        // 分隔文字為空：只用一個空格分隔 (A B)；有文字時前後各一個空格 (A | B)
        std::wstring sep = g_ovSeparator.empty() ? std::wstring(L" ") : (L" " + g_ovSeparator + L" ");
        std::wstring all;
        for (size_t i = 0; i < items.size(); ++i) {
            if (i) all += sep;
            all += items[i];
        }
        lines.push_back(all);
    } else {
        lines = items;
    }
}

// ---------------------------------------------------------------------------
//  疊加視窗：置頂、不搶焦點、逐像素透明；未鎖定時可拖曳，鎖定時滑鼠穿透
// ---------------------------------------------------------------------------
typedef UINT (WINAPI* pfnGetDpiForWindow)(HWND);

static int OverlayDpi() {
    static pfnGetDpiForWindow fn = (pfnGetDpiForWindow)GetProcAddress(GetModuleHandleW(L"user32.dll"), "GetDpiForWindow");
    if (fn && g_ovHwnd) {
        UINT d = fn(g_ovHwnd);
        if (d) return (int)d;
    }
    return 96;
}

struct MonEnum { std::wstring name; RECT rc; bool found; };

static BOOL CALLBACK MonEnumProc(HMONITOR hm, HDC, LPRECT, LPARAM lp) {
    MonEnum* e = (MonEnum*)lp;
    MONITORINFOEXW mi;
    ZeroMemory(&mi, sizeof(mi));
    mi.cbSize = sizeof(mi);
    if (GetMonitorInfoW(hm, (MONITORINFO*)&mi) && e->name == mi.szDevice) {
        e->rc = mi.rcMonitor;
        e->found = true;
        return FALSE;
    }
    return TRUE;
}

static RECT MonitorRectByName(const std::wstring& name) {
    MonEnum e;
    e.name = name;
    e.found = false;
    ZeroMemory(&e.rc, sizeof(e.rc));
    if (!name.empty()) EnumDisplayMonitors(NULL, NULL, MonEnumProc, (LPARAM)&e);
    if (e.found) return e.rc;
    POINT pt;
    pt.x = 0;
    pt.y = 0;
    HMONITOR hm = MonitorFromPoint(pt, MONITOR_DEFAULTTOPRIMARY);
    MONITORINFO mi;
    ZeroMemory(&mi, sizeof(mi));
    mi.cbSize = sizeof(mi);
    GetMonitorInfoW(hm, &mi);
    return mi.rcMonitor;
}

// 螢幕不見 (拔掉) 時退回主螢幕，並確保視窗左上角在螢幕內
static POINT OverlayPos() {
    RECT rc = MonitorRectByName(g_ovMonitor);
    POINT p;
    LONG x = std::min<LONG>(rc.left + g_ovX, rc.right - 60);
    LONG y = std::min<LONG>(rc.top + g_ovY, rc.bottom - 30);
    p.x = std::max<LONG>(x, rc.left);
    p.y = std::max<LONG>(y, rc.top);
    return p;
}

static void SaveOverlayPos() {
    RECT wr;
    if (!g_ovHwnd || !GetWindowRect(g_ovHwnd, &wr)) return;
    HMONITOR hm = MonitorFromWindow(g_ovHwnd, MONITOR_DEFAULTTONEAREST);
    MONITORINFOEXW mi;
    ZeroMemory(&mi, sizeof(mi));
    mi.cbSize = sizeof(mi);
    if (!GetMonitorInfoW(hm, (MONITORINFO*)&mi)) return;
    g_ovMonitor = mi.szDevice;
    g_ovX = std::max(0, (int)(wr.left - mi.rcMonitor.left));
    g_ovY = std::max(0, (int)(wr.top - mi.rcMonitor.top));
    if (!g_monDlgOpen) SaveOverlaySettings();   // 設定視窗開啟期間，到按下「確定」才寫入 ini
}

static bool InsideRounded(int x, int y, int w, int h, int r) {
    if (r <= 0) return true;
    int cx = (x < r) ? r : (x >= w - r ? w - r - 1 : x);
    int cy = (y < r) ? r : (y >= h - r ? h - r - 1 : y);
    int dx = x - cx, dy = y - cy;
    return dx * dx + dy * dy <= r * r;
}

static HBITMAP CreateDib32(HDC dc, int w, int h, void** bits) {
    BITMAPINFO bi;
    ZeroMemory(&bi, sizeof(bi));
    bi.bmiHeader.biSize = sizeof(BITMAPINFOHEADER);
    bi.bmiHeader.biWidth = w;
    bi.bmiHeader.biHeight = -h;   // 由上而下
    bi.bmiHeader.biPlanes = 1;
    bi.bmiHeader.biBitCount = 32;
    bi.bmiHeader.biCompression = BI_RGB;
    return CreateDIBSection(dc, &bi, DIB_RGB_COLORS, bits, NULL, 0);
}

// 設定視窗開啟時，如果沒有遊戲或沒有啟用監控，用示範數值預覽外觀
static OvSample DemoSample() {
    OvSample s;
    ZeroMemory(&s, sizeof(s));
    s.game = true;
    s.cpuOk = s.ghzOk = s.ramOk = s.gpuOk = s.vramOk = s.vramMbOk = s.fpsOk = s.latOk = true;
    s.cpu = 12.3;
    s.ghz = 5.31;
    s.ramPct = 8.1;
    s.ramMb = 5312;
    s.gpu = 38;
    s.vramPct = 26.8;
    s.vramMb = 3296;
    s.fps = 144;
    s.lat = 52;
    return s;
}

// 繪製流程：以 GDI 把白色文字畫到灰階遮罩 -> 膨脹出外框遮罩 -> 依文字色 / 外框色 / 背景合成預乘 Alpha 的 ARGB
static void RenderOverlay(bool force) {
    if (!g_ovHwnd) return;
    OvSample s;
    {
        std::lock_guard<std::mutex> lk(g_ovMtx);
        s = g_ovSample;
    }
    if (g_monDlgOpen && (!g_ovEnabled || !s.game)) s = DemoSample();
    std::vector<std::wstring> lines;
    BuildOverlayLines(s, lines);
    if (lines.empty()) return;

    int dpi = OverlayDpi();
    bool locked = g_ovLocked;
    // 背景：「鎖定時無背景」開啟時，鎖定 = 無背景、未鎖定 = 淺黑色半透明 (方便拖曳)；關閉時一律使用自訂背景色
    int bgMode = g_ovLockNoBg ? (locked ? 0 : 1) : 2;
    unsigned textC = g_ovTextColor, outC = g_ovOutlineColor, bgC = g_ovBgColor;
    int opacity = g_ovOpacity, fontPt = g_ovFontSize;

    std::wstring sig;
    for (size_t i = 0; i < lines.size(); ++i) {
        sig += lines[i];
        sig += L"\n";
    }
    wchar_t pb[200];
    wsprintfW(pb, L"|%d|%d|%d|%d|%u|%u|%u|%d|%d", dpi, fontPt, bgMode, (int)g_ovLayout, textC, outC, bgC, opacity, locked ? 1 : 0);
    sig += pb;
    if (!force && !g_ovPosDirty && sig == g_ovLastSig) return;
    g_ovLastSig = sig;

    int fontPx = std::max(8, MulDiv(fontPt, dpi, 72));
    int orad = std::max(1, std::min(3, fontPx / 12));   // 外框粗細 (像素)
    int pad = orad + 6;

    HDC screen = GetDC(NULL);
    HDC mem = CreateCompatibleDC(screen);
    HFONT font = CreateFontW(-fontPx, 0, 0, 0, FW_BOLD, FALSE, FALSE, FALSE, DEFAULT_CHARSET, OUT_DEFAULT_PRECIS,
                             CLIP_DEFAULT_PRECIS, ANTIALIASED_QUALITY, DEFAULT_PITCH | FF_DONTCARE, L"Segoe UI");
    HGDIOBJ oldFont = SelectObject(mem, font);
    TEXTMETRICW tm;
    ZeroMemory(&tm, sizeof(tm));
    GetTextMetricsW(mem, &tm);
    int lineH = (int)tm.tmHeight + 2;
    int maxW = 0;
    for (size_t i = 0; i < lines.size(); ++i) {
        SIZE sz;
        sz.cx = 0;
        sz.cy = 0;
        GetTextExtentPoint32W(mem, lines[i].c_str(), (int)lines[i].size(), &sz);
        maxW = std::max(maxW, (int)sz.cx);
    }
    int w = maxW + pad * 2;
    int h = lineH * (int)lines.size() + pad * 2;

    // 1) 文字遮罩 (白字畫在黑底上，灰階抗鋸齒；以綠色通道當覆蓋率)
    void* maskBits = NULL;
    HBITMAP hMask = CreateDib32(mem, w, h, &maskBits);
    HGDIOBJ oldBmp = SelectObject(mem, hMask);
    ZeroMemory(maskBits, (size_t)w * (size_t)h * 4);
    SetBkMode(mem, TRANSPARENT);
    SetTextColor(mem, RGB(255, 255, 255));
    for (size_t i = 0; i < lines.size(); ++i)
        TextOutW(mem, pad, pad + (int)i * lineH, lines[i].c_str(), (int)lines[i].size());
    GdiFlush();

    size_t npx = (size_t)w * (size_t)h;
    std::vector<unsigned char> m(npx), o(npx);
    const unsigned* src = (const unsigned*)maskBits;
    for (size_t i = 0; i < npx; ++i) m[i] = (unsigned char)((src[i] >> 8) & 0xFF);

    // 2) 外框遮罩：把文字遮罩向外膨脹 orad 像素 (圓形範圍)
    std::vector<std::pair<int, int> > kernel;
    for (int dy = -orad; dy <= orad; ++dy)
        for (int dx = -orad; dx <= orad; ++dx)
            if (dx * dx + dy * dy <= orad * orad + 1) kernel.push_back(std::make_pair(dx, dy));
    for (int y = 0; y < h; ++y) {
        for (int x = 0; x < w; ++x) {
            unsigned char mx = 0;
            for (size_t k = 0; k < kernel.size(); ++k) {
                int nx = x + kernel[k].first, ny = y + kernel[k].second;
                if (nx < 0 || ny < 0 || nx >= w || ny >= h) continue;
                unsigned char v = m[(size_t)ny * (size_t)w + (size_t)nx];
                if (v > mx) mx = v;
            }
            o[(size_t)y * (size_t)w + (size_t)x] = mx;
        }
    }

    // 3) 合成 (預乘 Alpha)：背景 <- 外框 <- 文字
    void* finalBits = NULL;
    HBITMAP hFinal = CreateDib32(mem, w, h, &finalBits);
    unsigned tr = (textC >> 16) & 0xFF, tg = (textC >> 8) & 0xFF, tb = textC & 0xFF;
    unsigned orr = (outC >> 16) & 0xFF, og = (outC >> 8) & 0xFF, ob = outC & 0xFF;
    unsigned bgA = 0, bgR = 0, bgG = 0, bgB = 0;
    if (bgMode == 1) {
        bgA = 90;   // 淺黑色半透明
    } else if (bgMode == 2) {
        bgA = 190;
        bgR = (bgC >> 16) & 0xFF;
        bgG = (bgC >> 8) & 0xFF;
        bgB = bgC & 0xFF;
    }
    unsigned pbR = bgR * bgA / 255, pbG = bgG * bgA / 255, pbB = bgB * bgA / 255;
    int corner = bgA ? std::min(fontPx / 2, 10) : 0;   // 背景圓角
    unsigned* dst = (unsigned*)finalBits;
    for (int y = 0; y < h; ++y) {
        for (int x = 0; x < w; ++x) {
            size_t i = (size_t)y * (size_t)w + (size_t)x;
            unsigned at = m[i], ao = o[i];
            unsigned aoUnder = ao * (255 - at) / 255;
            unsigned Al = at + aoUnder;
            unsigned Pr = (tr * at + orr * aoUnder) / 255;
            unsigned Pg = (tg * at + og * aoUnder) / 255;
            unsigned Pb = (tb * at + ob * aoUnder) / 255;
            unsigned ba = 0, qr = 0, qg = 0, qb = 0;
            if (bgA && InsideRounded(x, y, w, h, corner)) {
                ba = bgA;
                qr = pbR;
                qg = pbG;
                qb = pbB;
            }
            unsigned outA = Al + ba * (255 - Al) / 255;
            unsigned outR = Pr + qr * (255 - Al) / 255;
            unsigned outG = Pg + qg * (255 - Al) / 255;
            unsigned outB = Pb + qb * (255 - Al) / 255;
            if (outA > 255) outA = 255;
            outR = std::min(outR, outA);
            outG = std::min(outG, outA);
            outB = std::min(outB, outA);
            dst[i] = (outA << 24) | (outR << 16) | (outG << 8) | outB;
        }
    }

    // 4) 更新逐像素透明視窗
    HDC memF = CreateCompatibleDC(screen);
    HGDIOBJ oldF = SelectObject(memF, hFinal);
    POINT ptSrc;
    ptSrc.x = 0;
    ptSrc.y = 0;
    SIZE size;
    size.cx = w;
    size.cy = h;
    POINT ptDst;
    POINT* pDst = NULL;
    if (g_ovPosDirty) {
        ptDst = OverlayPos();
        pDst = &ptDst;
        g_ovPosDirty = false;
    }
    BLENDFUNCTION bf;
    bf.BlendOp = AC_SRC_OVER;
    bf.BlendFlags = 0;
    bf.SourceConstantAlpha = (BYTE)(255 * opacity / 100);
    bf.AlphaFormat = AC_SRC_ALPHA;
    UpdateLayeredWindow(g_ovHwnd, screen, pDst, &size, memF, &ptSrc, 0, &bf, ULW_ALPHA);

    SelectObject(memF, oldF);
    DeleteDC(memF);
    SelectObject(mem, oldBmp);
    SelectObject(mem, oldFont);
    DeleteObject(hMask);
    DeleteObject(hFinal);
    DeleteObject(font);
    DeleteDC(mem);
    ReleaseDC(NULL, screen);
}

static bool IsTaskbarClass(HWND w) {
    wchar_t cls[64];
    cls[0] = 0;
    GetClassNameW(w, cls, 64);
    return _wcsicmp(cls, L"Shell_TrayWnd") == 0 || _wcsicmp(cls, L"Shell_SecondaryTrayWnd") == 0 ||
           _wcsicmp(cls, L"TaskListThumbnailWnd") == 0 || _wcsicmp(cls, L"TaskListOverlayWnd") == 0 ||
           _wcsicmp(cls, L"XamlExplorerHostIslandWindow") == 0;
}

static void RaiseOverlay() {
    if (g_ovHwnd) SetWindowPos(g_ovHwnd, HWND_TOPMOST, 0, 0, 0, 0, SWP_NOMOVE | SWP_NOSIZE | SWP_NOACTIVATE);
}

// 是否有「工作列 / 縮圖預覽 / 遊戲視窗」蓋在監控視窗上面 (Z 順序比我們高，而且和我們有重疊)
static bool OverlayCovered() {
    RECT me;
    if (!g_ovHwnd || !GetWindowRect(g_ovHwnd, &me)) return false;
    DWORD gp = g_gamePid;
    int guard = 0;
    for (HWND w = GetWindow(g_ovHwnd, GW_HWNDPREV); w && guard < 300; w = GetWindow(w, GW_HWNDPREV), ++guard) {
        if (!IsWindowVisible(w)) continue;
        RECT r, inter;
        if (!GetWindowRect(w, &r) || !IntersectRect(&inter, &me, &r)) continue;
        DWORD pid = 0;
        GetWindowThreadProcessId(w, &pid);
        if (IsTaskbarClass(w) || (gp && pid == gp)) return true;
    }
    return false;
}

// 顯示規則：
//   * 設定視窗開啟期間固定顯示 (預覽)，不受「只在遊戲前景時顯示」影響
//   * 平常：啟用監控且遊戲執行中才顯示；遊戲最小化時隱藏
//   * 「只在遊戲前景時顯示」：前景不是遊戲就隱藏；但前景是本工具 (選單) 或工作列 / 縮圖預覽時維持原狀，避免閃爍
//   * 顯示期間每 40 毫秒檢查一次有沒有被工作列等視窗蓋住，被蓋住才立刻重新置頂
static void UpdateOverlayVisibility() {
    if (!g_ovHwnd) return;
    bool want = false;
    DWORD gp = g_gamePid;
    if (g_monDlgOpen) {
        want = HasAnyOverlayItem();
    } else if (g_ovEnabled && gp && HasAnyOverlayItem()) {
        want = true;
        if (g_gameHwnd && IsIconic(g_gameHwnd)) want = false;
        if (want && g_ovFgOnly) {
            HWND fg = GetForegroundWindow();
            DWORD fgPid = 0;
            if (fg) GetWindowThreadProcessId(fg, &fgPid);
            if (fg && (fgPid == GetCurrentProcessId() || IsTaskbarClass(fg))) return;   // 維持目前狀態
            want = (fgPid == gp);
        }
    }
    bool vis = IsWindowVisible(g_ovHwnd) != 0;
    if (want && !vis) {
        RenderOverlay(true);
        ShowWindow(g_ovHwnd, SW_SHOWNA);
        RaiseOverlay();
        SetTimer(g_ovHwnd, 3, 40, NULL);
    } else if (!want && vis) {
        KillTimer(g_ovHwnd, 3);
        ShowWindow(g_ovHwnd, SW_HIDE);
    } else if (want && vis) {
        if (OverlayCovered()) RaiseOverlay();
    }
}

static void ApplyOverlayLockStyle() {
    if (!g_ovHwnd) return;
    LONG_PTR ex = GetWindowLongPtrW(g_ovHwnd, GWL_EXSTYLE);
    if (g_ovLocked) ex |= WS_EX_TRANSPARENT;   // 鎖定：滑鼠穿透
    else ex &= ~(LONG_PTR)WS_EX_TRANSPARENT;
    SetWindowLongPtrW(g_ovHwnd, GWL_EXSTYLE, ex);
}

static LRESULT CALLBACK OverlayProc(HWND hwnd, UINT msg, WPARAM wp, LPARAM lp) {
    switch (msg) {
    case WM_NCHITTEST:
        return g_ovLocked ? HTCLIENT : HTCAPTION;   // 未鎖定：整個視窗都可拖曳
    case WM_MOUSEACTIVATE:
        return MA_NOACTIVATE;
    case WM_SETCURSOR:
        if (!g_ovLocked) {
            SetCursor(LoadCursorW(NULL, MAKEINTRESOURCEW(32646)));   // IDC_SIZEALL
            return TRUE;
        }
        break;
    case WM_EXITSIZEMOVE:
        SaveOverlayPos();
        g_ovLastSig.clear();
        RenderOverlay(true);   // 移到不同縮放的螢幕時，依新的 DPI 重繪
        return 0;
    case WM_DPICHANGED:
        g_ovLastSig.clear();
        RenderOverlay(true);
        return 0;
    case WM_TIMER:
        if (wp == 3 && IsWindowVisible(hwnd) && OverlayCovered()) RaiseOverlay();   // 被工作列等視窗蓋住時立刻奪回置頂
        return 0;
    }
    return DefWindowProcW(hwnd, msg, wp, lp);
}

// 工作列縮圖預覽 (Aero Peek) 會把其他視窗暫時隱藏；排除之後監控視窗不會跟著消失
static void ExcludeFromPeek(HWND h) {
    typedef HRESULT (WINAPI* pfnDwmSetWindowAttribute)(HWND, DWORD, LPCVOID, DWORD);
    HMODULE m = LoadLibraryW(L"dwmapi.dll");
    if (!m) return;
    pfnDwmSetWindowAttribute fn = (pfnDwmSetWindowAttribute)GetProcAddress(m, "DwmSetWindowAttribute");
    if (fn) {
        BOOL v = TRUE;
        fn(h, 12 /* DWMWA_EXCLUDED_FROM_PEEK */, &v, sizeof(v));
    }
}

static void CreateOverlayWindow() {
    WNDCLASSEXW wc;
    ZeroMemory(&wc, sizeof(wc));
    wc.cbSize = sizeof(wc);
    wc.lpfnWndProc = OverlayProc;
    wc.hInstance = g_hInst;
    wc.lpszClassName = L"MabinogiClientManagerOverlay";
    RegisterClassExW(&wc);
    POINT p = OverlayPos();
    DWORD ex = WS_EX_LAYERED | WS_EX_TOPMOST | WS_EX_TOOLWINDOW | WS_EX_NOACTIVATE;
    if (g_ovLocked) ex |= WS_EX_TRANSPARENT;
    g_ovHwnd = CreateWindowExW(ex, L"MabinogiClientManagerOverlay", L"ClientManagerOverlay", WS_POPUP, p.x, p.y, 10, 10, NULL, NULL, g_hInst, NULL);
    if (g_ovHwnd) ExcludeFromPeek(g_ovHwnd);
}

static void StartMonitor() {
    g_monRun = true;
    g_monThread = std::thread(MonitorThread);
}

static void StopMonitor() {
    g_monRun = false;
    if (g_monWake) SetEvent(g_monWake);
    if (g_monThread.joinable()) g_monThread.join();
}

// ---------------------------------------------------------------------------
//  監控設定視窗：套用 (立即變更監控畫面) / 確定 (儲存到 ini) / 取消 (回復到開啟前的狀態)
// ---------------------------------------------------------------------------
struct OvSettings {
    bool cpu, cpuPct, cpuGhz, ram, ramPct, ramMb, gpu, vram, vramPct, vramMb, fps, latency;
    bool enabled, fgOnly, locked, lockNoBg;
    int layout, intervalMs, fontSize, opacity, cpuMethod, latMethod, x, y;
    unsigned textColor, outlineColor, bgColor;
    std::wstring monitor, separator;
    std::vector<int> order;
};

static OvSettings CaptureOv() {
    OvSettings s;
    s.cpu = g_ovCpu;
    s.cpuPct = g_ovCpuPct;
    s.cpuGhz = g_ovCpuGhz;
    s.ram = g_ovRam;
    s.ramPct = g_ovRamPct;
    s.ramMb = g_ovRamMb;
    s.gpu = g_ovGpu;
    s.vram = g_ovVram;
    s.vramPct = g_ovVramPct;
    s.vramMb = g_ovVramMb;
    s.fps = g_ovFps;
    s.latency = g_ovLatency;
    s.enabled = g_ovEnabled;
    s.fgOnly = g_ovFgOnly;
    s.locked = g_ovLocked;
    s.lockNoBg = g_ovLockNoBg;
    s.layout = g_ovLayout;
    s.intervalMs = g_ovIntervalMs;
    s.fontSize = g_ovFontSize;
    s.opacity = g_ovOpacity;
    s.x = g_ovX;
    s.y = g_ovY;
    s.textColor = g_ovTextColor;
    s.outlineColor = g_ovOutlineColor;
    s.bgColor = g_ovBgColor;
    s.monitor = g_ovMonitor;
    s.cpuMethod = g_ovCpuMethod;
    s.latMethod = g_ovLatMethod;
    s.separator = g_ovSeparator;
    s.order = g_ovOrder;
    return s;
}

static void ApplyOvSettings(const OvSettings& s) {
    g_ovCpu = s.cpu;
    g_ovCpuPct = s.cpuPct;
    g_ovCpuGhz = s.cpuGhz;
    g_ovRam = s.ram;
    g_ovRamPct = s.ramPct;
    g_ovRamMb = s.ramMb;
    g_ovGpu = s.gpu;
    g_ovVram = s.vram;
    g_ovVramPct = s.vramPct;
    g_ovVramMb = s.vramMb;
    g_ovFps = s.fps;
    g_ovLatency = s.latency;
    g_ovEnabled = s.enabled;
    g_ovFgOnly = s.fgOnly;
    g_ovLocked = s.locked;
    g_ovLockNoBg = s.lockNoBg;
    g_ovLayout = s.layout;
    g_ovIntervalMs = s.intervalMs;
    g_ovFontSize = s.fontSize;
    g_ovOpacity = s.opacity;
    g_ovTextColor = s.textColor;
    g_ovOutlineColor = s.outlineColor;
    g_ovBgColor = s.bgColor;
    if (g_ovX != s.x || g_ovY != s.y || g_ovMonitor != s.monitor) g_ovPosDirty = true;   // 位置有變 (例如取消時回復)
    g_ovX = s.x;
    g_ovY = s.y;
    g_ovMonitor = s.monitor;
    g_ovCpuMethod = s.cpuMethod;
    g_ovLatMethod = s.latMethod;
    g_ovSeparator = s.separator;
    g_ovOrder = s.order;
}

// 立即反映到監控畫面 (不寫入 ini)
static void OverlayRefresh() {
    if (g_monWake) SetEvent(g_monWake);   // 取樣執行緒依新的項目 / 頻率重新取樣
    UpdateFpsSession();
    ApplyOverlayLockStyle();
    g_ovLastSig.clear();
    UpdateOverlayVisibility();
    if (g_ovHwnd && IsWindowVisible(g_ovHwnd)) RenderOverlay(true);
}

static void OverlayChanged() {
    SaveOverlaySettings();
    OverlayRefresh();
}

enum MonDlgIds {
    MD_CPU = 2001, MD_CPU_PCT, MD_CPU_ACT, MD_RAM, MD_RAM_PCT, MD_RAM_ACT, MD_GPU, MD_VRAM, MD_VRAM_PCT, MD_VRAM_ACT, MD_FPS, MD_LAT,
    MD_ENABLE, MD_LAYOUT, MD_SEP, MD_INTERVAL, MD_METHOD, MD_LATMETHOD, MD_ORDER, MD_FONT, MD_TEXTCOLOR, MD_TEXTSWATCH, MD_OUTLINE, MD_OUTSWATCH, MD_OPACITY, MD_BGCOLOR, MD_BGSWATCH,
    MD_LOCKNOBG, MD_FGONLY, MD_LOCK, MD_RESETPOS, MD_APPLY
};

struct MonDlgCtx {
    OvSettings before;   // 開啟視窗時的狀態 (按取消時回復)
    HBRUSH sw[3];        // 三個色塊預覽用的筆刷
    int dragIdx;         // 順序清單拖曳中的項目
    int insertPos;       // 順序清單目前顯示插入線的位置 (-1 = 沒有)
};

static const int kOvIntervals[] = { 500, 1000, 2000 };
static const int kOvIntervalCount = (int)(sizeof(kOvIntervals) / sizeof(kOvIntervals[0]));
static const int kOvFontSizes[] = { 10, 12, 14, 16, 18, 20, 24 };
static const int kOvFontCount = (int)(sizeof(kOvFontSizes) / sizeof(kOvFontSizes[0]));
static const int kOvOpacities[] = { 100, 90, 80, 70, 60, 50, 40 };
static const int kOvOpacityCount = (int)(sizeof(kOvOpacities) / sizeof(kOvOpacities[0]));

static bool DlgChecked(HWND dlg, int id) {
    return SendDlgItemMessageW(dlg, id, BM_GETCHECK, 0, 0) == BST_CHECKED;
}

static void DlgSetChecked(HWND dlg, int id, bool v) {
    CheckDlgButton(dlg, id, v ? BST_CHECKED : BST_UNCHECKED);
}

static void ComboAdd(HWND dlg, int id, const wchar_t* label, int value) {
    LRESULT i = SendDlgItemMessageW(dlg, id, CB_ADDSTRING, 0, (LPARAM)label);
    SendDlgItemMessageW(dlg, id, CB_SETITEMDATA, (WPARAM)i, (LPARAM)value);
}

static int ComboValue(HWND dlg, int id, int def) {
    LRESULT sel = SendDlgItemMessageW(dlg, id, CB_GETCURSEL, 0, 0);
    if (sel < 0) return def;
    return (int)SendDlgItemMessageW(dlg, id, CB_GETITEMDATA, (WPARAM)sel, 0);
}

// kind：0 = 字體大小、1 = 不透明度、2 = 更新頻率
static std::wstring ComboLabel(int kind, int v) {
    wchar_t b[48];
    if (kind == 0) {
        wsprintfW(b, L"%d pt", v);
    } else if (kind == 1) {
        wsprintfW(b, L"%d%%", v);
    } else {
        if (v == 500) return T(S_MON_EVERY_05);
        if (v == 1000) return T(S_MON_EVERY_1);
        if (v == 2000) return T(S_MON_EVERY_2);
        wsprintfW(b, L"%d ms", v);
    }
    return b;
}

// 下拉選單列出預設值；目前的值如果不在預設值裡 (例如手動改了 ini)，會多加一個項目保留原值，不會被改掉
static void ComboFill(HWND dlg, int id, const int* vals, int n, int cur, int kind) {
    int sel = -1;
    for (int i = 0; i < n; ++i) {
        ComboAdd(dlg, id, ComboLabel(kind, vals[i]).c_str(), vals[i]);
        if (vals[i] == cur) sel = i;
    }
    if (sel < 0) {
        ComboAdd(dlg, id, ComboLabel(kind, cur).c_str(), cur);
        sel = n;
    }
    SendDlgItemMessageW(dlg, id, CB_SETCURSEL, (WPARAM)sel, 0);
}

static void UpdateSwatch(HWND dlg, MonDlgCtx* c, int idx) {
    static const int editIds[3] = { MD_TEXTCOLOR, MD_OUTLINE, MD_BGCOLOR };
    static const int swIds[3] = { MD_TEXTSWATCH, MD_OUTSWATCH, MD_BGSWATCH };
    wchar_t b[32];
    b[0] = 0;
    GetDlgItemTextW(dlg, editIds[idx], b, 32);
    unsigned v;
    COLORREF col = ParseHex6(b, &v) ? RGB((v >> 16) & 0xFF, (v >> 8) & 0xFF, v & 0xFF) : RGB(200, 200, 200);
    if (c->sw[idx]) DeleteObject(c->sw[idx]);
    c->sw[idx] = CreateSolidBrush(col);
    InvalidateRect(GetDlgItem(dlg, swIds[idx]), NULL, TRUE);
}

// 讀取視窗上的所有設定；色碼格式不對時提示並回傳 false
static bool ReadMonDlg(HWND dlg, OvSettings& s) {
    s = CaptureOv();   // 位置等不在視窗上的項目沿用目前的值
    s.cpu = DlgChecked(dlg, MD_CPU);
    s.cpuPct = DlgChecked(dlg, MD_CPU_PCT);
    s.cpuGhz = DlgChecked(dlg, MD_CPU_ACT);
    s.ram = DlgChecked(dlg, MD_RAM);
    s.ramPct = DlgChecked(dlg, MD_RAM_PCT);
    s.ramMb = DlgChecked(dlg, MD_RAM_ACT);
    s.gpu = DlgChecked(dlg, MD_GPU);
    s.vram = DlgChecked(dlg, MD_VRAM);
    s.vramPct = DlgChecked(dlg, MD_VRAM_PCT);
    s.vramMb = DlgChecked(dlg, MD_VRAM_ACT);
    s.fps = DlgChecked(dlg, MD_FPS);
    s.latency = DlgChecked(dlg, MD_LAT);
    s.layout = ComboValue(dlg, MD_LAYOUT, s.layout);
    s.cpuMethod = ComboValue(dlg, MD_METHOD, s.cpuMethod);
    s.latMethod = ComboValue(dlg, MD_LATMETHOD, s.latMethod);
    s.enabled = DlgChecked(dlg, MD_ENABLE);
    {
        wchar_t sb[32];
        sb[0] = 0;
        GetDlgItemTextW(dlg, MD_SEP, sb, 32);
        std::wstring sp = sb;
        while (!sp.empty() && sp[0] == L' ') sp.erase(0, 1);
        while (!sp.empty() && sp[sp.size() - 1] == L' ') sp.erase(sp.size() - 1, 1);
        s.separator = sp;
        s.order.clear();
        int cnt = (int)SendDlgItemMessageW(dlg, MD_ORDER, LB_GETCOUNT, 0, 0);
        for (int i = 0; i < cnt; ++i) s.order.push_back((int)SendDlgItemMessageW(dlg, MD_ORDER, LB_GETITEMDATA, (WPARAM)i, 0));
    }
    s.intervalMs = ComboValue(dlg, MD_INTERVAL, s.intervalMs);
    s.fontSize = ComboValue(dlg, MD_FONT, s.fontSize);
    s.opacity = ComboValue(dlg, MD_OPACITY, s.opacity);
    s.lockNoBg = DlgChecked(dlg, MD_LOCKNOBG);
    s.fgOnly = DlgChecked(dlg, MD_FGONLY);
    s.locked = DlgChecked(dlg, MD_LOCK);
    static const int ids[3] = { MD_TEXTCOLOR, MD_OUTLINE, MD_BGCOLOR };
    unsigned cols[3];
    for (int i = 0; i < 3; ++i) {
        wchar_t b[32];
        b[0] = 0;
        GetDlgItemTextW(dlg, ids[i], b, 32);
        if (!ParseHex6(b, &cols[i])) {
            MessageBoxW(dlg, T(S_DLG_COLOR_BAD), L"Mabinogi Client Manager", MB_OK | MB_ICONWARNING);
            SetFocus(GetDlgItem(dlg, ids[i]));
            return false;
        }
    }
    s.textColor = cols[0];
    s.outlineColor = cols[1];
    s.bgColor = cols[2];
    return true;
}

static void ClearDebugText() {
    {
        std::lock_guard<std::mutex> lk(g_dbgMtx);
        g_cpuDbg.clear();
        g_latDbg.clear();
    }
    std::lock_guard<std::mutex> lk(g_etwDbgMtx);
    g_etwSeen.clear();
}

// 在順序清單的第 pos 項之前畫一條插入線 (pos = 項目數 → 最後一項之後；pos < 0 → 清除)
static void ShowInsertLine(HWND lb, MonDlgCtx* c, int pos) {
    if (c->insertPos == pos) return;
    c->insertPos = pos;
    InvalidateRect(lb, NULL, TRUE);
    UpdateWindow(lb);
    int count = (int)SendMessageW(lb, LB_GETCOUNT, 0, 0);
    if (pos < 0 || count <= 0) return;
    RECT ir, cr;
    ZeroMemory(&ir, sizeof(ir));
    int y;
    if (pos >= count) {
        SendMessageW(lb, LB_GETITEMRECT, (WPARAM)(count - 1), (LPARAM)&ir);
        y = ir.bottom;
    } else {
        SendMessageW(lb, LB_GETITEMRECT, (WPARAM)pos, (LPARAM)&ir);
        y = ir.top;
    }
    GetClientRect(lb, &cr);
    if (y < 1) y = 1;
    if (y > cr.bottom - 2) y = cr.bottom - 2;
    HDC dc = GetDC(lb);
    if (dc) {
        HPEN pen = CreatePen(PS_SOLID, 2, GetSysColor(COLOR_HIGHLIGHT));
        HGDIOBJ old = SelectObject(dc, pen);
        MoveToEx(dc, cr.left + 2, y, NULL);
        LineTo(dc, cr.right - 2, y);
        SelectObject(dc, old);
        DeleteObject(pen);
        ReleaseDC(lb, dc);
    }
}

static void CopyTextToClipboard(HWND owner, const std::wstring& text) {
    if (!OpenClipboard(owner)) return;
    EmptyClipboard();
    size_t bytes = (text.size() + 1) * sizeof(wchar_t);
    HGLOBAL h = GlobalAlloc(GMEM_MOVEABLE, bytes);
    if (h) {
        void* p = GlobalLock(h);
        if (p) {
            memcpy(p, text.c_str(), bytes);
            GlobalUnlock(h);
            if (!SetClipboardData(CF_UNICODETEXT, h)) GlobalFree(h);
        } else {
            GlobalFree(h);
        }
    }
    CloseClipboard();
}

static UINT g_dragListMsg = 0;   // 拖曳清單的通知訊息 (comctl32 的 MakeDragList)

// 把清單中第 from 項移到第 to 項之前 (to = 0..項目數)
static void ListMove(HWND lb, int from, int to) {
    int count = (int)SendMessageW(lb, LB_GETCOUNT, 0, 0);
    if (from < 0 || from >= count || to < 0 || to > count) return;
    if (to == from || to == from + 1) return;
    wchar_t buf[64];
    buf[0] = 0;
    SendMessageW(lb, LB_GETTEXT, (WPARAM)from, (LPARAM)buf);
    LRESULT data = SendMessageW(lb, LB_GETITEMDATA, (WPARAM)from, 0);
    SendMessageW(lb, LB_DELETESTRING, (WPARAM)from, 0);
    int pos = (to > from) ? to - 1 : to;
    LRESULT idx = SendMessageW(lb, LB_INSERTSTRING, (WPARAM)pos, (LPARAM)buf);
    SendMessageW(lb, LB_SETITEMDATA, (WPARAM)idx, (LPARAM)data);
    SendMessageW(lb, LB_SETCURSEL, (WPARAM)idx, 0);
}

static INT_PTR CALLBACK MonDlgProc(HWND dlg, UINT msg, WPARAM wp, LPARAM lp) {
    MonDlgCtx* c = (MonDlgCtx*)GetWindowLongPtrW(dlg, GWLP_USERDATA);
    if (g_dragListMsg && msg == g_dragListMsg && c && lp) {
        DRAGLISTINFO* di = (DRAGLISTINFO*)lp;
        HWND lb = di->hWnd;
        int count = (int)SendMessageW(lb, LB_GETCOUNT, 0, 0);
        LRESULT res = 0;
        auto itemAt = [&](POINT pt) -> int {
            int it = LBItemFromPt(lb, pt, TRUE);
            if (it < 0) {   // 清單的空白處 = 放到最後
                POINT p = pt;
                ScreenToClient(lb, &p);
                RECT rc;
                GetClientRect(lb, &rc);
                if (PtInRect(&rc, p)) it = count;
            }
            return it;
        };
        switch (di->uNotification) {
        case DL_BEGINDRAG:
            c->dragIdx = LBItemFromPt(lb, di->ptCursor, TRUE);
            res = (c->dragIdx >= 0) ? TRUE : FALSE;
            break;
        case DL_DRAGGING: {
            int it = itemAt(di->ptCursor);
            ShowInsertLine(lb, c, it);
            res = (it >= 0) ? DL_MOVECURSOR : DL_STOPCURSOR;
            break;
        }
        case DL_DROPPED: {
            int it = itemAt(di->ptCursor);
            ShowInsertLine(lb, c, -1);
            if (it >= 0 && c->dragIdx >= 0) ListMove(lb, c->dragIdx, it);
            c->dragIdx = -1;
            break;
        }
        case DL_CANCELDRAG:
            ShowInsertLine(lb, c, -1);
            c->dragIdx = -1;
            break;
        }
        SetWindowLongPtrW(dlg, DWLP_MSGRESULT, res);
        return TRUE;
    }
    switch (msg) {
    case WM_INITDIALOG: {
        c = (MonDlgCtx*)lp;
        SetWindowLongPtrW(dlg, GWLP_USERDATA, (LONG_PTR)c);
        g_monDlgHwnd = dlg;
        const OvSettings& s = c->before;
        DlgSetChecked(dlg, MD_CPU, s.cpu);
        DlgSetChecked(dlg, MD_CPU_PCT, s.cpuPct);
        DlgSetChecked(dlg, MD_CPU_ACT, s.cpuGhz);
        DlgSetChecked(dlg, MD_RAM, s.ram);
        DlgSetChecked(dlg, MD_RAM_PCT, s.ramPct);
        DlgSetChecked(dlg, MD_RAM_ACT, s.ramMb);
        DlgSetChecked(dlg, MD_GPU, s.gpu);
        DlgSetChecked(dlg, MD_VRAM, s.vram);
        DlgSetChecked(dlg, MD_VRAM_PCT, s.vramPct);
        DlgSetChecked(dlg, MD_VRAM_ACT, s.vramMb);
        DlgSetChecked(dlg, MD_FPS, s.fps);
        DlgSetChecked(dlg, MD_ENABLE, s.enabled);
        DlgSetChecked(dlg, MD_LAT, s.latency);
        DlgSetChecked(dlg, MD_LOCKNOBG, s.lockNoBg);
        DlgSetChecked(dlg, MD_FGONLY, s.fgOnly);
        DlgSetChecked(dlg, MD_LOCK, s.locked);
        ComboAdd(dlg, MD_LAYOUT, T(S_MON_VERT), 0);
        ComboAdd(dlg, MD_LAYOUT, T(S_MON_HORZ), 1);
        SendDlgItemMessageW(dlg, MD_LAYOUT, CB_SETCURSEL, (WPARAM)(s.layout == 1 ? 1 : 0), 0);
        SetDlgItemTextW(dlg, MD_SEP, s.separator.c_str());
        SendDlgItemMessageW(dlg, MD_SEP, EM_LIMITTEXT, 12, 0);
        EnableWindow(GetDlgItem(dlg, MD_SEP), s.layout == 1);   // 分隔文字只有橫式用得到
        ComboAdd(dlg, MD_METHOD, T(S_METHOD_CYC), 0);
        ComboAdd(dlg, MD_METHOD, T(S_METHOD_TIME), 1);
        ComboAdd(dlg, MD_METHOD, T(S_METHOD_EST), 2);
        SendDlgItemMessageW(dlg, MD_METHOD, CB_SETCURSEL, (WPARAM)((s.cpuMethod >= 0 && s.cpuMethod <= 2) ? s.cpuMethod : 0), 0);
        ComboAdd(dlg, MD_LATMETHOD, T(S_LAT_SAMPLE), 0);
        ComboAdd(dlg, MD_LATMETHOD, T(S_LAT_SMOOTH), 1);
        SendDlgItemMessageW(dlg, MD_LATMETHOD, CB_SETCURSEL, (WPARAM)(s.latMethod == 1 ? 1 : 0), 0);
        for (size_t i = 0; i < s.order.size(); ++i) {
            LRESULT idx = SendDlgItemMessageW(dlg, MD_ORDER, LB_ADDSTRING, 0, (LPARAM)kOvItemNames[s.order[i]]);
            SendDlgItemMessageW(dlg, MD_ORDER, LB_SETITEMDATA, (WPARAM)idx, (LPARAM)s.order[i]);
        }
        MakeDragList(GetDlgItem(dlg, MD_ORDER));   // 可用滑鼠拖曳調整顯示順序
        ComboFill(dlg, MD_INTERVAL, kOvIntervals, kOvIntervalCount, s.intervalMs, 2);
        ComboFill(dlg, MD_FONT, kOvFontSizes, kOvFontCount, s.fontSize, 0);
        ComboFill(dlg, MD_OPACITY, kOvOpacities, kOvOpacityCount, s.opacity, 1);
        SetDlgItemTextW(dlg, MD_TEXTCOLOR, Hex6(s.textColor).c_str());
        SetDlgItemTextW(dlg, MD_OUTLINE, Hex6(s.outlineColor).c_str());
        SetDlgItemTextW(dlg, MD_BGCOLOR, Hex6(s.bgColor).c_str());
        static const int editIds[3] = { MD_TEXTCOLOR, MD_OUTLINE, MD_BGCOLOR };
        for (int i = 0; i < 3; ++i) {
            SendDlgItemMessageW(dlg, editIds[i], EM_LIMITTEXT, 7, 0);
            UpdateSwatch(dlg, c, i);
        }
        OverlayRefresh();   // 開啟設定視窗：固定顯示監控畫面 (預覽)
        return TRUE;
    }
    case WM_CTLCOLORSTATIC: {
        int id = GetDlgCtrlID((HWND)lp);
        if (c && id == MD_TEXTSWATCH && c->sw[0]) return (INT_PTR)c->sw[0];
        if (c && id == MD_OUTSWATCH && c->sw[1]) return (INT_PTR)c->sw[1];
        if (c && id == MD_BGSWATCH && c->sw[2]) return (INT_PTR)c->sw[2];
        break;
    }
    case WM_COMMAND: {
        int id = LOWORD(wp);
        int code = HIWORD(wp);
        if (id == MD_LAYOUT && code == CBN_SELCHANGE) {
            EnableWindow(GetDlgItem(dlg, MD_SEP), ComboValue(dlg, MD_LAYOUT, 0) == 1);
            return TRUE;
        }
        if (code == EN_CHANGE && c) {
            if (id == MD_TEXTCOLOR) UpdateSwatch(dlg, c, 0);
            else if (id == MD_OUTLINE) UpdateSwatch(dlg, c, 1);
            else if (id == MD_BGCOLOR) UpdateSwatch(dlg, c, 2);
            return TRUE;
        }
        if (id == MD_APPLY) {
            OvSettings s;
            if (ReadMonDlg(dlg, s)) {
                ApplyOvSettings(s);
                OverlayRefresh();   // 立即變更監控畫面，尚未寫入 ini
            }
            return TRUE;
        }
        if (id == MD_RESETPOS) {
            g_ovX = 20;
            g_ovY = 20;
            g_ovMonitor.clear();
            g_ovPosDirty = true;
            OverlayRefresh();
            return TRUE;
        }
        if (id == IDOK) {
            OvSettings s;
            if (!ReadMonDlg(dlg, s)) return TRUE;
            ApplyOvSettings(s);
            SaveOverlaySettings();   // 按下確定才寫入 ini
            EndDialog(dlg, IDOK);
            return TRUE;
        }
        if (id == IDCANCEL) {
            if (c) ApplyOvSettings(c->before);   // 回復到開啟視窗之前的狀態
            EndDialog(dlg, IDCANCEL);
            return TRUE;
        }
        break;
    }
    case WM_DESTROY:
        if (c) {
            for (int i = 0; i < 3; ++i) {
                if (c->sw[i]) DeleteObject(c->sw[i]);
                c->sw[i] = NULL;
            }
        }
        g_monDlgHwnd = NULL;
        break;
    }
    return FALSE;
}

static void TmplAlign(std::vector<WORD>& v) {
    if (v.size() & 1) v.push_back(0);
}

static void TmplStr(std::vector<WORD>& v, const wchar_t* s) {
    while (*s) v.push_back((WORD)*s++);
    v.push_back(0);
}

static void TmplItem(std::vector<WORD>& v, DWORD style, short x, short y, short cx, short cy, WORD id, WORD classAtom, const wchar_t* text) {
    TmplAlign(v);
    v.push_back((WORD)(style & 0xFFFF));
    v.push_back((WORD)(style >> 16));
    v.push_back(0);
    v.push_back(0);   // 擴充樣式
    v.push_back((WORD)x);
    v.push_back((WORD)y);
    v.push_back((WORD)cx);
    v.push_back((WORD)cy);
    v.push_back(id);
    v.push_back(0xFFFF);
    v.push_back(classAtom);   // 0x0080 按鈕、0x0081 編輯、0x0082 靜態文字、0x0085 下拉式方塊
    TmplStr(v, text);
    v.push_back(0);   // 沒有建立資料
}

static HWND g_aboutDlg = NULL;   // 「關於」視窗 (開著時不開監控設定)

static void ShowMonitorSettings() {
    if (g_monDlgOpen) {
        if (g_monDlgHwnd) SetForegroundWindow(g_monDlgHwnd);
        return;
    }
    if (g_aboutDlg) {
        SetForegroundWindow(g_aboutDlg);
        return;
    }
    MonDlgCtx ctx;
    ctx.before = CaptureOv();
    ctx.sw[0] = ctx.sw[1] = ctx.sw[2] = NULL;
    ctx.dragIdx = -1;
    ctx.insertPos = -1;
    if (!g_dragListMsg) g_dragListMsg = RegisterWindowMessageW(L"commctrl_DragListMsg");

    const WORD BTN = 0x0080, EDT = 0x0081, STC = 0x0082, CMB = 0x0085, NOID = 0xFFFF;
    std::vector<WORD> t;
    DWORD style = DS_MODALFRAME | DS_SETFONT | DS_CENTER | DS_SETFOREGROUND | WS_POPUP | WS_CAPTION | WS_SYSMENU;
    t.push_back((WORD)(style & 0xFFFF));
    t.push_back((WORD)(style >> 16));
    t.push_back(0);
    t.push_back(0);                 // 擴充樣式
    size_t cditPos = t.size();
    t.push_back(0);                 // 控制項數量 (稍後填入)
    t.push_back(0);
    t.push_back(0);                 // x, y
    t.push_back(330);
    t.push_back(396);               // cx, cy (對話框單位)
    t.push_back(0);                 // 選單
    t.push_back(0);                 // 類別
    TmplStr(t, T(S_DLG_MON_TITLE));
    t.push_back(9);                 // 字型大小
    TmplStr(t, L"Segoe UI");

    int n = 0;
    auto add = [&](DWORD st, int x, int y, int cx, int cy, WORD id, WORD cls, const wchar_t* text) {
        TmplItem(t, WS_CHILD | WS_VISIBLE | st, (short)x, (short)y, (short)cx, (short)cy, id, cls, text);
        ++n;
    };
    const DWORD CHK = BS_AUTOCHECKBOX | WS_TABSTOP;
    const DWORD COMBO = WS_TABSTOP | WS_VSCROLL | CBS_DROPDOWNLIST;
    const DWORD HEXEDIT = WS_TABSTOP | WS_BORDER | ES_AUTOHSCROLL | ES_UPPERCASE;
    const DWORD HEXEDIT_PLAIN = WS_TABSTOP | WS_BORDER | ES_AUTOHSCROLL;

    const WORD LST = 0x0083;
    const DWORD LISTBOX = LBS_NOTIFY | LBS_NOINTEGRALHEIGHT | WS_BORDER | WS_TABSTOP;

    // 啟用監控 (最上方)
    add(CHK, 8, 6, 250, 12, MD_ENABLE, BTN, T(S_MON_ENABLE));

    // 顯示項目 (左) 與顯示順序 (右，用滑鼠拖曳調整)
    add(BS_GROUPBOX, 8, 22, 212, 106, NOID, BTN, T(S_MON_ITEMS));
    add(CHK, 14, 36, 38, 12, MD_CPU, BTN, L"CPU");
    add(CHK, 54, 36, 44, 12, MD_CPU_PCT, BTN, T(S_MON_PCT));
    add(CHK, 100, 36, 116, 12, MD_CPU_ACT, BTN, T(S_MON_ACTUAL_GHZ));
    add(CHK, 14, 50, 38, 12, MD_RAM, BTN, L"RAM");
    add(CHK, 54, 50, 44, 12, MD_RAM_PCT, BTN, T(S_MON_PCT));
    add(CHK, 100, 50, 116, 12, MD_RAM_ACT, BTN, T(S_MON_ACTUAL_MB));
    add(CHK, 14, 64, 100, 12, MD_GPU, BTN, L"GPU");
    add(CHK, 14, 78, 38, 12, MD_VRAM, BTN, L"VRAM");
    add(CHK, 54, 78, 44, 12, MD_VRAM_PCT, BTN, T(S_MON_PCT));
    add(CHK, 100, 78, 116, 12, MD_VRAM_ACT, BTN, T(S_MON_ACTUAL_MB));
    add(CHK, 14, 92, 100, 12, MD_FPS, BTN, L"FPS");
    add(CHK, 14, 106, 100, 12, MD_LAT, BTN, L"Latency");
    add(BS_GROUPBOX, 224, 22, 98, 106, NOID, BTN, T(S_MON_ORDER));
    add(LISTBOX, 230, 36, 86, 86, MD_ORDER, LST, L"");

    // 顯示設定：排列方式 (橫式可設定分隔文字)、更新頻率、CPU 使用率算法
    add(BS_GROUPBOX, 8, 130, 314, 84, NOID, BTN, T(S_MON_DISPLAY));
    add(SS_LEFT, 16, 144, 68, 10, NOID, STC, T(S_MON_LAYOUT));
    add(COMBO, 88, 142, 100, 80, MD_LAYOUT, CMB, L"");
    add(SS_LEFT, 194, 144, 44, 10, NOID, STC, T(S_MON_SEPARATOR));
    add(HEXEDIT_PLAIN, 240, 142, 72, 12, MD_SEP, EDT, L"");
    add(SS_LEFT, 16, 162, 68, 10, NOID, STC, T(S_MON_INTERVAL));
    add(COMBO, 88, 160, 224, 80, MD_INTERVAL, CMB, L"");
    add(SS_LEFT, 16, 180, 68, 10, NOID, STC, T(S_MON_METHOD));
    add(COMBO, 88, 178, 224, 80, MD_METHOD, CMB, L"");
    add(SS_LEFT, 16, 198, 68, 10, NOID, STC, T(S_MON_LATMETHOD));
    add(COMBO, 88, 196, 224, 80, MD_LATMETHOD, CMB, L"");

    // 外觀
    add(BS_GROUPBOX, 8, 218, 314, 114, NOID, BTN, T(S_MON_STYLE));
    add(SS_LEFT, 16, 234, 90, 10, NOID, STC, T(S_MON_FONTSIZE));
    add(COMBO, 110, 232, 90, 80, MD_FONT, CMB, L"");
    add(SS_LEFT, 16, 250, 90, 10, NOID, STC, T(S_LBL_TEXTCOLOR));
    add(HEXEDIT, 110, 248, 52, 12, MD_TEXTCOLOR, EDT, L"");
    add(WS_BORDER | SS_LEFT, 168, 248, 14, 12, MD_TEXTSWATCH, STC, L"");
    add(SS_LEFT, 16, 266, 90, 10, NOID, STC, T(S_LBL_OUTLINECOLOR));
    add(HEXEDIT, 110, 264, 52, 12, MD_OUTLINE, EDT, L"");
    add(WS_BORDER | SS_LEFT, 168, 264, 14, 12, MD_OUTSWATCH, STC, L"");
    add(SS_LEFT, 16, 282, 90, 10, NOID, STC, T(S_MON_OPACITY));
    add(COMBO, 110, 280, 90, 80, MD_OPACITY, CMB, L"");
    add(SS_LEFT, 16, 298, 90, 10, NOID, STC, T(S_LBL_BGCOLOR));
    add(HEXEDIT, 110, 296, 52, 12, MD_BGCOLOR, EDT, L"");
    add(WS_BORDER | SS_LEFT, 168, 296, 14, 12, MD_BGSWATCH, STC, L"");
    add(CHK, 16, 312, 290, 12, MD_LOCKNOBG, BTN, T(S_MON_LOCKNOBG));

    // 其他
    add(CHK, 8, 338, 314, 12, MD_FGONLY, BTN, T(S_MON_FGONLY_DLG));
    add(CHK, 8, 354, 220, 12, MD_LOCK, BTN, T(S_MON_LOCK));
    add(BS_PUSHBUTTON | WS_TABSTOP, 236, 352, 86, 14, MD_RESETPOS, BTN, T(S_MON_RESETPOS));

    // 確定 / 取消 / 套用
    add(BS_DEFPUSHBUTTON | WS_TABSTOP, 170, 374, 48, 14, IDOK, BTN, T(S_DLG_OK));
    add(BS_PUSHBUTTON | WS_TABSTOP, 222, 374, 48, 14, IDCANCEL, BTN, T(S_DLG_CANCEL));
    add(BS_PUSHBUTTON | WS_TABSTOP, 274, 374, 48, 14, MD_APPLY, BTN, T(S_DLG_APPLY));
    t[cditPos] = (WORD)n;

    g_monDlgOpen = true;
    DialogBoxIndirectParamW(g_hInst, (LPCDLGTEMPLATEW)t.data(), g_hWnd, MonDlgProc, (LPARAM)&ctx);
    g_monDlgOpen = false;
    OverlayRefresh();   // 關閉後依「只在遊戲前景時顯示」等設定重新判斷
}

// ---------------------------------------------------------------------------
//  選單 / 命令
// ---------------------------------------------------------------------------
static UINT Chk(bool v) { return v ? MF_CHECKED : 0; }

static void BuildMonitorMenu(HMENU parent) {
    HMENU mon = CreatePopupMenu();
    AppendMenuW(mon, MF_STRING | Chk(g_ovEnabled), ID_OV_ENABLE, T(S_MON_ENABLE));
    AppendMenuW(mon, MF_STRING | Chk(g_ovLocked), ID_OV_LOCK, T(S_MON_LOCK));
    AppendMenuW(mon, MF_STRING, ID_OV_SETTINGS, T(S_MON_SETTINGS));
    AppendMenuW(parent, MF_POPUP, (UINT_PTR)mon, T(S_M_MON));
}

static void HandleOverlayCommand(int id) {
    if (id == ID_OV_SETTINGS) {
        ShowMonitorSettings();
        return;
    }
    if (g_monDlgOpen) {   // 設定視窗開啟期間，其他監控選項請在視窗內調整
        if (g_monDlgHwnd) SetForegroundWindow(g_monDlgHwnd);
        return;
    }
    if (id == ID_OV_ENABLE) g_ovEnabled = !g_ovEnabled;
    else if (id == ID_OV_LOCK) g_ovLocked = !g_ovLocked;
    OverlayChanged();
}


// ---------------------------------------------------------------------------
//  遊戲未啟動的提示視窗
//  已記錄過遊戲路徑與啟動參數時，多提供「重啟 Client.exe」「重啟 Mabinogi.exe」兩個按鈕
// ---------------------------------------------------------------------------
static INT_PTR CALLBACK NoGameDlgProc(HWND dlg, UINT msg, WPARAM wp, LPARAM lp) {
    switch (msg) {
    case WM_INITDIALOG:
        return TRUE;
    case WM_COMMAND: {
        int id = LOWORD(wp);
        if (id == 101 || id == 102 || id == IDCANCEL) {
            EndDialog(dlg, id);
            return TRUE;
        }
        break;
    }
    }
    return FALSE;
}

static void ShowNoGameDialog() {
    if (g_noGameDlgOpen) return;
    std::wstring path = GetCachedPath();
    bool canRestart = !path.empty() && !GetCachedArgs().empty() && FileExists(path);
    bool hasLauncher = false;
    if (canRestart) {
        std::wstring dir = DirOf(path);
        hasLauncher = FileExists(dir + L"\\Mabinogi.exe") || FileExists(dir + L"\\mabinogi.exe");
    }
    const WORD BTN = 0x0080, STC = 0x0082, NOID = 0xFFFF;
    std::vector<WORD> t;
    DWORD style = DS_MODALFRAME | DS_SETFONT | DS_CENTER | DS_SETFOREGROUND | WS_POPUP | WS_CAPTION | WS_SYSMENU;
    t.push_back((WORD)(style & 0xFFFF));
    t.push_back((WORD)(style >> 16));
    t.push_back(0x0008);
    t.push_back(0);                 // 擴充樣式：WS_EX_TOPMOST
    size_t cditPos = t.size();
    t.push_back(0);                 // 控制項數量 (稍後填入)
    t.push_back(0);
    t.push_back(0);                 // x, y
    t.push_back(262);
    t.push_back(66);                // cx, cy
    t.push_back(0);
    t.push_back(0);
    TmplStr(t, L"Mabinogi Client Manager");
    t.push_back(9);
    TmplStr(t, L"Segoe UI");
    int n = 0;
    auto add = [&](DWORD st, int x, int y, int cx, int cy, WORD id, WORD cls, const wchar_t* text) {
        TmplItem(t, WS_CHILD | WS_VISIBLE | st, (short)x, (short)y, (short)cx, (short)cy, id, cls, text);
        ++n;
    };
    add(SS_LEFT, 10, 10, 242, 28, NOID, STC, T(S_NO_GAME));
    if (canRestart) {
        add(BS_PUSHBUTTON | WS_TABSTOP, 10, 46, 86, 14, 101, BTN, T(S_DLG_RESTART_CLIENT));
        if (hasLauncher) add(BS_PUSHBUTTON | WS_TABSTOP, 100, 46, 94, 14, 102, BTN, T(S_DLG_RESTART_LAUNCHER));
        add(BS_DEFPUSHBUTTON | WS_TABSTOP, 202, 46, 50, 14, IDCANCEL, BTN, T(S_DLG_CLOSE));
    } else {
        add(BS_DEFPUSHBUTTON | WS_TABSTOP, 106, 46, 50, 14, IDCANCEL, BTN, T(S_DLG_CLOSE));
    }
    t[cditPos] = (WORD)n;
    g_noGameDlgOpen = true;
    INT_PTR r = DialogBoxIndirectParamW(g_hInst, (LPCDLGTEMPLATEW)t.data(), g_hWnd, NoGameDlgProc, 0);
    g_noGameDlgOpen = false;
    if (r == 101) StartRestart(false);
    else if (r == 102) StartRestart(true);
}

// 連點兩下通知區域圖示：先確認遊戲是否在執行，沒有就顯示上面的提示視窗
static void OnTrayDoubleClick() {
    if (GetClientPids().empty()) {
        ShowNoGameDialog();
        return;
    }
    int a = g_dblAction;
    if (a == 1) {
        g_cpuEnabled = !g_cpuEnabled;
        SaveInt(L"CpuEnabled", g_cpuEnabled ? 1 : 0);
        WakeEngine();
    } else if (a == 2) {
        HandleOverlayCommand(ID_OV_ENABLE);
    } else {
        ToggleBorderless();
    }
}
// ---------------------------------------------------------------------------
//  關於視窗：程式說明 + 診斷記錄
//  診斷記錄只在這個視窗開啟期間收集 (不寫入檔案)，預設自動更新，可按「停止更新」手動暫停；
//  在記錄區塊內選取文字、或捲動捲軸時也會暫停，回到最上方 / 最左邊且沒有選取時才恢復自動更新
// ---------------------------------------------------------------------------
enum { AB_LOG = 3001, AB_COPY, AB_PAUSE };

struct AboutCtx {
    HFONT font;
    bool paused;
    std::wstring lastLog;
};

// 記錄區塊正在被使用者操作 (選取文字 / 捲動) 時不更新內容
static bool AboutLogBusy(HWND ed) {
    DWORD selStart = 0, selEnd = 0;
    SendMessageW(ed, EM_GETSEL, (WPARAM)&selStart, (LPARAM)&selEnd);
    if (GetFocus() == ed && selStart != selEnd) return true;
    SCROLLINFO si;
    ZeroMemory(&si, sizeof(si));
    si.cbSize = sizeof(si);
    si.fMask = SIF_POS;
    if (GetScrollInfo(ed, SB_VERT, &si) && si.nPos != 0) return true;
    ZeroMemory(&si, sizeof(si));
    si.cbSize = sizeof(si);
    si.fMask = SIF_POS;
    if (GetScrollInfo(ed, SB_HORZ, &si) && si.nPos != 0) return true;
    return false;
}

static void UpdateAboutLog(HWND dlg, AboutCtx* c) {
    if (!c || c->paused) return;
    HWND ed = GetDlgItem(dlg, AB_LOG);
    if (AboutLogBusy(ed)) return;
    std::wstring txt = BuildDebugText();
    if (txt != c->lastLog) {
        c->lastLog = txt;
        SetWindowTextW(ed, txt.c_str());
    }
}

static INT_PTR CALLBACK AboutDlgProc(HWND dlg, UINT msg, WPARAM wp, LPARAM lp) {
    AboutCtx* c = (AboutCtx*)GetWindowLongPtrW(dlg, GWLP_USERDATA);
    switch (msg) {
    case WM_INITDIALOG:
        c = (AboutCtx*)lp;
        SetWindowLongPtrW(dlg, GWLP_USERDATA, (LONG_PTR)c);
        g_aboutDlg = dlg;
        c->font = CreateFontW(-MulDiv(9, OverlayDpi(), 72), 0, 0, 0, FW_NORMAL, FALSE, FALSE, FALSE, DEFAULT_CHARSET,
                              OUT_DEFAULT_PRECIS, CLIP_DEFAULT_PRECIS, DEFAULT_QUALITY, FIXED_PITCH | FF_MODERN, L"Consolas");
        if (c->font) SendDlgItemMessageW(dlg, AB_LOG, WM_SETFONT, (WPARAM)c->font, TRUE);
        SetTimer(dlg, 1, 1000, NULL);   // 診斷記錄每秒更新一次
        UpdateAboutLog(dlg, c);
        SetFocus(GetDlgItem(dlg, IDCANCEL));   // 不讓記錄區塊一開啟就取得焦點 (會全選文字而暫停更新)
        return FALSE;
    case WM_TIMER:
        UpdateAboutLog(dlg, c);
        return TRUE;
    case WM_COMMAND: {
        int id = LOWORD(wp);
        if (id == AB_COPY) {
            CopyTextToClipboard(dlg, BuildDebugText());   // 立即複製目前的記錄
            return TRUE;
        }
        if (id == AB_PAUSE && c) {
            c->paused = !c->paused;
            SetDlgItemTextW(dlg, AB_PAUSE, T(c->paused ? S_DLG_AUTO_UPDATE : S_DLG_STOP_UPDATE));
            if (!c->paused) UpdateAboutLog(dlg, c);
            return TRUE;
        }
        if (id == IDCANCEL || id == IDOK) {
            EndDialog(dlg, id);
            return TRUE;
        }
        break;
    }
    case WM_DESTROY:
        KillTimer(dlg, 1);
        if (c && c->font) {
            DeleteObject(c->font);
            c->font = NULL;
        }
        g_aboutDlg = NULL;
        break;
    }
    return FALSE;
}

static void ShowAboutDialog() {
    if (g_aboutDlg) {
        SetForegroundWindow(g_aboutDlg);
        return;
    }
    if (g_monDlgOpen) {
        if (g_monDlgHwnd) SetForegroundWindow(g_monDlgHwnd);
        return;
    }
    const WORD BTN = 0x0080, EDT = 0x0081, STC = 0x0082, NOID = 0xFFFF;
    std::vector<WORD> t;
    DWORD style = DS_MODALFRAME | DS_SETFONT | DS_CENTER | DS_SETFOREGROUND | WS_POPUP | WS_CAPTION | WS_SYSMENU;
    t.push_back((WORD)(style & 0xFFFF));
    t.push_back((WORD)(style >> 16));
    t.push_back(0);
    t.push_back(0);                 // 擴充樣式：無
    size_t cditPos = t.size();
    t.push_back(0);                 // 控制項數量 (稍後填入)
    t.push_back(0);
    t.push_back(0);                 // x, y
    t.push_back(330);
    t.push_back(308);               // cx, cy (對話框單位)
    t.push_back(0);
    t.push_back(0);
    TmplStr(t, T(S_ABOUT_TITLE));
    t.push_back(9);
    TmplStr(t, L"Segoe UI");
    int n = 0;
    auto add = [&](DWORD st, int x, int y, int cx, int cy, WORD id, WORD cls, const wchar_t* text) {
        TmplItem(t, WS_CHILD | WS_VISIBLE | st, (short)x, (short)y, (short)cx, (short)cy, id, cls, text);
        ++n;
    };
    std::wstring aboutText = std::wstring(L"Mabinogi Client Manager  ") + T(S_ABOUT_VERSION) + L" " + APP_VERSION_WSTR + L"\n\n" + T(S_ABOUT_TEXT);
    const DWORD LOGEDIT = ES_MULTILINE | ES_READONLY | ES_AUTOVSCROLL | ES_AUTOHSCROLL | WS_VSCROLL | WS_HSCROLL | WS_BORDER | WS_TABSTOP;
    add(BS_GROUPBOX, 8, 6, 314, 120, NOID, BTN, T(S_ABOUT_GROUP));
    add(SS_LEFT, 14, 18, 302, 104, NOID, STC, aboutText.c_str());
    add(BS_GROUPBOX, 8, 130, 314, 148, NOID, BTN, T(S_MON_DEBUG));
    add(LOGEDIT, 14, 142, 302, 112, AB_LOG, EDT, L"");
    add(BS_PUSHBUTTON | WS_TABSTOP, 14, 258, 50, 14, AB_COPY, BTN, T(S_DLG_COPY));
    add(BS_PUSHBUTTON | WS_TABSTOP, 68, 258, 64, 14, AB_PAUSE, BTN, T(S_DLG_STOP_UPDATE));
    add(BS_DEFPUSHBUTTON | WS_TABSTOP, 274, 286, 48, 14, IDCANCEL, BTN, T(S_DLG_CLOSE));
    t[cditPos] = (WORD)n;

    AboutCtx ctx;
    ctx.font = NULL;
    ctx.paused = false;
    g_ovDebug = true;   // 診斷記錄只在關於視窗開啟期間收集
    ClearDebugText();
    if (g_monWake) SetEvent(g_monWake);
    DialogBoxIndirectParamW(g_hInst, (LPCDLGTEMPLATEW)t.data(), g_hWnd, AboutDlgProc, (LPARAM)&ctx);
    g_ovDebug = false;
}

// ---------------------------------------------------------------------------
//  名稱 / 通知區域提示 (滑鼠停留在通知區域圖示上時才更新，不需要背景輪詢)
// ---------------------------------------------------------------------------
static const wchar_t* PrioName(int lv) { return T(S_PRIO_1 + lv - 1); }
static const wchar_t* IoName(int lv) { return T(S_IO_1 + lv - 1); }

static std::wstring CoreTypeText(int core) {
    switch (g_coreType[core]) {
    case 1: return T(S_CORE_P);
    case 2: return TS(S_CORE_P_HT);
    case 3: return T(S_CORE_E);
    case 4: return TS(S_CORE_E_HT);
    case 5: return T(S_CORE_PHYS);
    case 6: return TS(S_CORE_HT);
    }
    return L"";
}

static std::wstring MaskToText(unsigned long long m) {
    std::wstring r;
    int i = 0;
    while (i < 64) {
        if (!((m >> i) & 1)) {
            ++i;
            continue;
        }
        int j = i;
        while (j + 1 < 64 && ((m >> (j + 1)) & 1)) ++j;
        wchar_t b[32];
        if (j > i) wsprintfW(b, L"%d-%d", i, j);
        else wsprintfW(b, L"%d", i);
        if (!r.empty()) r += L", ";
        r += b;
        i = j + 1;
    }
    return r.empty() ? std::wstring(L"?") : r;
}

// 工具提示文字 (通知區域圖示的提示最多 127 字元)：
//   Mabinogi Client Manager (限制中)
//   (空行)
//   目前的遊戲優先權 / 親和性
//   CPU: ... / GPU: ... / I/O: ... / 核心: ...
static std::wstring BuildTip() {
    std::wstring head = L"Mabinogi Client Manager";
    if (g_throttleOn) head += T(S_TIP_LIMITING);
    if (!g_showTip) return head;
    std::vector<DWORD> pids = GetClientPids();
    if (pids.empty()) return head + L"\n\n" + T(S_TIP_NOGAME);
    DWORD pid = pids[0];
    std::wstring cpuName = L"?", gpuName = L"?", ioName = L"?", cores = L"?";
    HANDLE h = OpenProcess(PROCESS_QUERY_INFORMATION | PROCESS_QUERY_LIMITED_INFORMATION, FALSE, pid);
    if (h) {
        int lv = LevelFromPrioClass(GetPriorityClass(h));
        if (lv) cpuName = PrioName(lv);
        DWORD_PTR pm = 0, sm = 0;
        if (GetProcessAffinityMask(h, &pm, &sm) && pm) cores = MaskToText((unsigned long long)pm);
        int io = ReadIoHint(h);
        if (io >= 0) ioName = IoName(io + 1);
        CloseHandle(h);
    }
    LONG st = 0;
    int gc = ReadGpuClassPid(pid, &st);
    if (gc >= 0) {
        gpuName = PrioName(gc + 1);
    } else {
        wchar_t e[32];
        wsprintfW(e, L"?(%08X)", (unsigned int)st);   // 讀取失敗時附上系統狀態碼，方便診斷
        gpuName = e;
    }
    DWORD perr = g_prioErr;
    if (perr) {
        wchar_t e[32];
        wsprintfW(e, L" [!%lu]", (unsigned long)perr);   // 最近一次設定 CPU 優先權失敗的錯誤碼
        cpuName += e;
    }
    wchar_t buf[200];
    std::wstring body;
    wsprintfW(buf, T(S_TIP_CPU), cpuName.c_str());
    body += buf;
    wsprintfW(buf, T(S_TIP_GPU), gpuName.c_str());
    body += L"\n";
    body += buf;
    wsprintfW(buf, T(S_TIP_IO), ioName.c_str());
    body += L"\n";
    body += buf;
    wsprintfW(buf, T(S_TIP_CORES), cores.c_str());
    body += L"\n";
    body += buf;
    std::wstring hdr = T(S_TIP_HEADER);
    // 超過 127 字元時依序省略：空行、標題行 (核心清單在最後，最後才會被截斷)
    std::wstring full = head + L"\n\n" + hdr + L"\n" + body;
    if (full.size() <= 127) return full;
    full = head + L"\n" + hdr + L"\n" + body;
    if (full.size() <= 127) return full;
    return head + L"\n" + body;
}

static void ApplyTrayState() {
    g_nid.uFlags = NIF_ICON | NIF_MESSAGE | NIF_TIP;
    g_nid.hIcon = g_throttleOn ? g_iconBlue : g_iconNormal;
    std::wstring tip = BuildTip();
    lstrcpynW(g_nid.szTip, tip.c_str(), 128);
    Shell_NotifyIconW(NIM_MODIFY, &g_nid);
}

static bool CursorOnTrayIcon() {
    NOTIFYICONIDENTIFIER nii;
    ZeroMemory(&nii, sizeof(nii));
    nii.cbSize = sizeof(nii);
    nii.hWnd = g_hWnd;
    nii.uID = 1;
    RECT r;
    if (!SUCCEEDED(Shell_NotifyIconGetRect(&nii, &r))) return false;
    POINT p;
    GetCursorPos(&p);
    return PtInRect(&r, p) != 0;
}

static ULONGLONG g_lastTipTick = 0;

// 滑鼠移到通知區域圖示上時 (系統會傳來 WM_MOUSEMOVE) 更新提示；停留期間每 2 秒再更新一次，離開後自動停止
static void OnTrayHover() {
    ULONGLONG now = GetTickCount64();
    if (now - g_lastTipTick >= 800) {
        g_lastTipTick = now;
        ApplyTrayState();
    }
    SetTimer(g_hWnd, 2, 2000, NULL);
}

// ---------------------------------------------------------------------------
//  選單
// ---------------------------------------------------------------------------
// 優先權等級由高到低顯示 (上面高、下面低)
static void AddLevelMenu(HMENU parent, const wchar_t* title, bool io, int maxLevel, int baseId, int current) {
    HMENU sub = CreatePopupMenu();
    for (int lv = maxLevel; lv >= 1; --lv)
        AppendMenuW(sub, MF_STRING | (current == lv ? MF_CHECKED : 0), baseId + lv, io ? IoName(lv) : PrioName(lv));
    AppendMenuW(parent, MF_POPUP, (UINT_PTR)sub, title);
}

static void ShowMenu(HWND hwnd) {
    POINT pt;
    GetCursorPos(&pt);
    int mode = g_mode;
    int ratio = g_ratio;
    HMENU m = CreatePopupMenu();
    AppendMenuW(m, MF_STRING | (g_borderless ? MF_CHECKED : 0), ID_TOGGLE, T(S_M_TOGGLE));
    AppendMenuW(m, MF_STRING | (g_locked ? MF_CHECKED : 0), ID_LOCK, T(S_M_LOCK));
    AppendMenuW(m, MF_STRING, ID_RESET, T(S_M_RESET));
    AppendMenuW(m, MF_SEPARATOR, 0, NULL);

    HMENU adv = CreatePopupMenu();
    AddLevelMenu(adv, T(S_M_CPUPRIO), false, 6, ID_PRIO_CPU_BASE, g_cfgCpuPrio);

    HMENU aff = CreatePopupMenu();
    unsigned long long curMask = g_cfgAffMask;
    AppendMenuW(aff, MF_STRING, ID_AFF_ALL, T(S_AFF_ALL));
    if (g_hybrid) {
        AppendMenuW(aff, MF_STRING, ID_AFF_P, T(S_AFF_P));
        AppendMenuW(aff, MF_STRING, ID_AFF_PNOHT, TS(S_AFF_PNOHT).c_str());
        AppendMenuW(aff, MF_STRING, ID_AFF_E, T(S_AFF_E));
    } else if (g_maskPnoHT != g_maskAll) {
        AppendMenuW(aff, MF_STRING, ID_AFF_PNOHT, TS(S_AFF_NOHT).c_str());   // 有超執行緒 / SMT 的一般 CPU
    }
    AppendMenuW(aff, MF_SEPARATOR, 0, NULL);
    for (int i = 0; i < g_coreCount; ++i) {
        if (!((g_maskAll >> i) & 1)) continue;
        wchar_t label[200];
        std::wstring ct = CoreTypeText(i);
        wsprintfW(label, T(S_CORE_ITEM), i, ct.c_str());
        AppendMenuW(aff, MF_STRING | (((curMask >> i) & 1) ? MF_CHECKED : 0), ID_AFFCORE_BASE + i, label);
    }
    AppendMenuW(adv, MF_POPUP, (UINT_PTR)aff, T(S_M_CPUAFF));

    AddLevelMenu(adv, T(S_M_GPUPRIO), false, 6, ID_GPU_BASE, g_cfgGpuPrio);
    AddLevelMenu(adv, T(S_M_IOPRIO), true, 4, ID_IO_BASE, g_cfgIoPrio);
    AppendMenuW(adv, MF_SEPARATOR, 0, NULL);
    AppendMenuW(adv, MF_STRING | (g_showTip ? MF_CHECKED : 0), ID_SHOWTIP, T(S_M_TIPSHOW));
    AppendMenuW(m, MF_POPUP, (UINT_PTR)adv, T(S_M_GAMEPRIO));

    HMENU cpu = CreatePopupMenu();
    AppendMenuW(cpu, MF_STRING | (g_cpuEnabled ? MF_CHECKED : 0), ID_CPU_ENABLE, T(S_M_ENABLE));
    AppendMenuW(cpu, MF_STRING | (g_eco ? MF_CHECKED : 0), ID_ECO, T(S_M_ECO));
    HMENU cond = CreatePopupMenu();
    AppendMenuW(cond, MF_STRING | (mode == 1 ? MF_CHECKED : 0), ID_CPU_ALW, T(S_C_ALWAYS));
    AppendMenuW(cond, MF_STRING | (mode == 2 ? MF_CHECKED : 0), ID_CPU_MIN, T(S_C_MIN));
    AppendMenuW(cond, MF_STRING | (mode == 3 ? MF_CHECKED : 0), ID_CPU_BG, T(S_C_BG));
    AppendMenuW(cpu, MF_POPUP, (UINT_PTR)cond, T(S_M_COND));
    HMENU rm = CreatePopupMenu();
    for (int i = 0; i < kRatioCount; ++i) {
        wchar_t label[16];
        wsprintfW(label, L"%d%%", kRatios[i]);
        AppendMenuW(rm, MF_STRING | (ratio == kRatios[i] ? MF_CHECKED : 0), ID_RATIO_BASE + i, label);
    }
    AppendMenuW(cpu, MF_POPUP, (UINT_PTR)rm, T(S_M_RATIO));
    AppendMenuW(m, MF_POPUP, (UINT_PTR)cpu, T(S_M_LIMIT));
    BuildMonitorMenu(m);
    AppendMenuW(m, MF_SEPARATOR, 0, NULL);

    HMENU rs = CreatePopupMenu();
    AppendMenuW(rs, MF_STRING, ID_RESTART_CLIENT, T(S_M_RESTART_CLIENT));
    AppendMenuW(rs, MF_STRING, ID_RESTART_LAUNCHER, T(S_M_RESTART_LAUNCHER));
    AppendMenuW(rs, MF_STRING, ID_TERM, T(S_M_TERM));
    AppendMenuW(m, MF_POPUP, (UINT_PTR)rs, T(S_M_RESTARTMENU));
    AppendMenuW(m, MF_SEPARATOR, 0, NULL);

    HMENU dbl = CreatePopupMenu();
    int da = g_dblAction;
    AppendMenuW(dbl, MF_STRING | (da == 0 ? MF_CHECKED : 0), ID_DBL_BASE + 0, T(S_M_TOGGLE));
    AppendMenuW(dbl, MF_STRING | (da == 1 ? MF_CHECKED : 0), ID_DBL_BASE + 1, T(S_DBL_CPU));
    AppendMenuW(dbl, MF_STRING | (da == 2 ? MF_CHECKED : 0), ID_DBL_BASE + 2, T(S_DBL_MON));
    AppendMenuW(m, MF_POPUP, (UINT_PTR)dbl, T(S_M_DBLCLICK));

    HMENU lang = CreatePopupMenu();
    int sel = g_langSetting;
    AppendMenuW(lang, MF_STRING | (sel == UL_AUTO ? MF_CHECKED : 0), ID_LANG_BASE + UL_AUTO, T(S_L_AUTO));
    AppendMenuW(lang, MF_STRING | (sel == UL_ZHTW ? MF_CHECKED : 0), ID_LANG_BASE + UL_ZHTW, L"繁體中文 Chinese Traditional");
    AppendMenuW(lang, MF_STRING | (sel == UL_ZHCN ? MF_CHECKED : 0), ID_LANG_BASE + UL_ZHCN, L"简体中文 Chinese Simplified");
    AppendMenuW(lang, MF_STRING | (sel == UL_EN ? MF_CHECKED : 0), ID_LANG_BASE + UL_EN, L"英文 English");
    AppendMenuW(lang, MF_STRING | (sel == UL_JA ? MF_CHECKED : 0), ID_LANG_BASE + UL_JA, L"日本語 Japanese");
    AppendMenuW(m, MF_POPUP, (UINT_PTR)lang, T(S_M_LANG));
    AppendMenuW(m, MF_STRING, ID_ABOUT, T(S_M_ABOUT));
    AppendMenuW(m, MF_STRING, ID_EXIT, T(S_M_EXIT));

    SetForegroundWindow(hwnd);
    TrackPopupMenu(m, TPM_BOTTOMALIGN | TPM_LEFTALIGN, pt.x, pt.y, 0, hwnd, NULL);
    PostMessageW(hwnd, WM_NULL, 0, 0);
    DestroyMenu(m);
}

static void HandleCommand(int id) {
    switch (id) {
    case ID_TOGGLE: ToggleBorderless(); break;
    case ID_RESET: ResetWindow(); break;
    case ID_LOCK: ToggleLock(); break;
    case ID_CPU_ENABLE:
        g_cpuEnabled = !g_cpuEnabled;
        SaveInt(L"CpuEnabled", g_cpuEnabled ? 1 : 0);
        WakeEngine();
        break;
    case ID_CPU_ALW: SetMode(1); break;
    case ID_CPU_MIN: SetMode(2); break;
    case ID_CPU_BG: SetMode(3); break;
    case ID_ECO:
        g_eco = !g_eco;
        SaveInt(L"Eco", g_eco ? 1 : 0);
        WakeEngine();
        break;
    case ID_SHOWTIP:
        g_showTip = !g_showTip;
        SaveInt(L"ShowTip", g_showTip ? 1 : 0);
        ApplyTrayState();
        break;
    case ID_AFF_ALL: SetAffMask((unsigned long long)g_maskAll); break;
    case ID_AFF_P: SetAffMask((unsigned long long)g_maskP); break;
    case ID_AFF_PNOHT: SetAffMask((unsigned long long)g_maskPnoHT); break;
    case ID_AFF_E: SetAffMask((unsigned long long)g_maskE); break;
    case ID_RESTART_CLIENT: StartRestart(false); break;
    case ID_RESTART_LAUNCHER: StartRestart(true); break;
    case ID_TERM:
        if (GetClientPids().empty()) ShowNoGameDialog();
        else TerminateAllClients(0);
        break;
    case ID_ABOUT:
        ShowAboutDialog();
        break;
    case ID_EXIT:
        DestroyWindow(g_hWnd);
        break;
    default:
        if (id >= ID_RATIO_BASE && id < ID_RATIO_BASE + kRatioCount) {
            g_ratio = kRatios[id - ID_RATIO_BASE];
            SaveInt(L"Ratio", g_ratio);
            WakeEngine();
        } else if (id > ID_PRIO_CPU_BASE && id <= ID_PRIO_CPU_BASE + 6) {
            SetCfg(g_cfgCpuPrio, L"CpuPriority", id - ID_PRIO_CPU_BASE);
            ApplyBaseToAll();
        } else if (id > ID_GPU_BASE && id <= ID_GPU_BASE + 6) {
            SetCfg(g_cfgGpuPrio, L"GpuPriority", id - ID_GPU_BASE);
            ApplyBaseToAll();
        } else if (id > ID_IO_BASE && id <= ID_IO_BASE + 4) {
            SetCfg(g_cfgIoPrio, L"IoPriority", id - ID_IO_BASE);
            ApplyBaseToAll();
        } else if (id >= ID_AFFCORE_BASE && id < ID_AFFCORE_BASE + 64) {
            // 切換單一核心：尚未設定時，以「全部核心」為起點
            unsigned long long cur = g_cfgAffMask;
            if (cur == 0) cur = (unsigned long long)g_maskAll;
            unsigned long long nm = (cur ^ (1ULL << (id - ID_AFFCORE_BASE))) & (unsigned long long)g_maskAll;
            if (nm == 0) Notify(T(S_NEED_ONE_CORE));
            else SetAffMask(nm);
        } else if (id >= ID_DBL_BASE && id <= ID_DBL_BASE + 2) {
            g_dblAction = id - ID_DBL_BASE;
            SaveInt(L"DoubleClick", g_dblAction);
        } else if (id >= ID_OV_ENABLE && id <= ID_OV_LAST) {
            HandleOverlayCommand(id);
        } else if (id >= ID_LANG_BASE && id <= ID_LANG_BASE + 4) {
            g_langSetting = id - ID_LANG_BASE;
            ApplyLanguage();
            SaveString(L"Language", LangName(g_langSetting));
            ApplyTrayState();
        }
        break;
    }
}

static LRESULT CALLBACK WndProc(HWND hwnd, UINT msg, WPARAM wp, LPARAM lp) {
    if (g_wmTaskbarCreated && msg == g_wmTaskbarCreated) {
        Shell_NotifyIconW(NIM_ADD, &g_nid);   // explorer 重啟後補回通知區域圖示
        return 0;
    }
    switch (msg) {
    case WM_TRAYICON:
        if (lp == WM_RBUTTONUP) ShowMenu(hwnd);
        else if (lp == WM_LBUTTONDBLCLK) OnTrayDoubleClick();
        else if (lp == WM_MOUSEMOVE) OnTrayHover();
        return 0;
    case WM_TIMER:
        if (wp == 1) {
            SyncWindows();
        } else if (wp == 4) {
            RegrayAllLocked();
            if (--g_regrayLeft <= 0) KillTimer(hwnd, 4);
        } else if (wp == 5) {
            KillTimer(hwnd, 5);
            ModeCheck();
        } else if (wp == 2) {
            if (CursorOnTrayIcon()) ApplyTrayState();   // 仍停留在圖示上：更新提示
            else KillTimer(hwnd, 2);                    // 已離開：停止更新
        }
        return 0;
    case WM_UI_REAPPLY:
        ApplyBaseSettings((DWORD)wp);
        return 0;
    case WM_UI_THROTTLE:
        g_throttleOn = (wp != 0);
        ApplyTrayState();
        if (g_ovHwnd && IsWindowVisible(g_ovHwnd)) RenderOverlay(false);   // 「(限制中)」標示隨狀態更新
        return 0;
    case WM_UI_OVERLAY:
        UpdateOverlayVisibility();
        if (g_ovHwnd && IsWindowVisible(g_ovHwnd)) RenderOverlay(false);
        return 0;
    case WM_COMMAND:
        HandleCommand((int)LOWORD(wp));
        return 0;
    case WM_QUERYENDSESSION:
        return TRUE;
    case WM_ENDSESSION:
        if (wp) ShutdownEngine();
        return 0;
    case WM_DESTROY:
        PostQuitMessage(0);
        return 0;
    }
    return DefWindowProcW(hwnd, msg, wp, lp);
}

// ---------------------------------------------------------------------------
//  進入點
// ---------------------------------------------------------------------------
int APIENTRY WinMain(HINSTANCE hInstance, HINSTANCE, LPSTR, int) {
    g_hInst = hInstance;
    HMODULE hNt = GetModuleHandleW(L"ntdll.dll");
    if (hNt) {
        g_NtSuspend = (pfnNtProc)GetProcAddress(hNt, "NtSuspendProcess");
        g_NtResume = (pfnNtProc)GetProcAddress(hNt, "NtResumeProcess");
        g_NtQuery = (pfnNtQueryInformationProcess)GetProcAddress(hNt, "NtQueryInformationProcess");
        g_NtSetInfo = (pfnNtSetInformationProcess)GetProcAddress(hNt, "NtSetInformationProcess");
    }
    HMODULE hK = GetModuleHandleW(L"kernel32.dll");
    if (hK) g_SetProcInfo = (pfnSetProcessInformation)GetProcAddress(hK, "SetProcessInformation");
    HMODULE hGdi = LoadLibraryW(L"gdi32.dll");
    if (hGdi) {
        g_D3dkmtSetPrio = (pfnD3dkmtSetPriority)GetProcAddress(hGdi, "D3DKMTSetProcessSchedulingPriorityClass");
        g_D3dkmtGetPrio = (pfnD3dkmtGetPriority)GetProcAddress(hGdi, "D3DKMTGetProcessSchedulingPriorityClass");
    }

    // 救援參數：ClientManager.exe /resume  只解除遊戲暫停後離開
    if (wcsstr(GetCommandLineW(), L"/resume") != NULL) {
        ResumeAllClients();
        return 0;
    }

    g_mutex = CreateMutexW(NULL, TRUE, L"MabinogiClientManager_Mutex");
    if (!g_mutex || GetLastError() == ERROR_ALREADY_EXISTS) {
        LoadSettings();
        ApplyLanguage();
        MessageBoxW(NULL, T(S_ALREADY_RUNNING), L"Mabinogi Client Manager", MB_OK | MB_ICONINFORMATION);
        return 0;
    }

    // 讓座標與縮放比例 (125%/150%) 下的視窗計算正確
    HMODULE hU = GetModuleHandleW(L"user32.dll");
    if (hU) {
        pfnSetProcessDpiAwarenessContext setDpi = (pfnSetProcessDpiAwarenessContext)GetProcAddress(hU, "SetProcessDpiAwarenessContext");
        if (setDpi) setDpi((HANDLE)-4);   // PER_MONITOR_AWARE_V2
    }

    SetUnhandledExceptionFilter(CrashFilter);
    EnablePrivilege(L"SeIncreaseBasePriorityPrivilege");   // 設定即時優先權 / 高 I/O 優先權需要
    InitCpuTopology();
    LARGE_INTEGER fq;
    QueryPerformanceFrequency(&fq);
    g_qpcFreq = (double)fq.QuadPart;

    LoadSettings();
    ApplyLanguage();

    g_wake = CreateEventW(NULL, FALSE, FALSE, NULL);
    g_pauseAck = CreateEventW(NULL, TRUE, FALSE, NULL);
    g_monWake = CreateEventW(NULL, FALSE, FALSE, NULL);
    g_timer = CreateWaitableTimerExW(NULL, NULL, CREATE_WAITABLE_TIMER_HIGH_RESOLUTION, SYNCHRONIZE | TIMER_MODIFY_STATE);
    g_hiRes = (g_timer != NULL);
    if (!g_timer) g_timer = CreateWaitableTimerW(NULL, FALSE, NULL);

    g_wmTaskbarCreated = RegisterWindowMessageW(L"TaskbarCreated");

    WNDCLASSEXW wc;
    ZeroMemory(&wc, sizeof(wc));
    wc.cbSize = sizeof(wc);
    wc.lpfnWndProc = WndProc;
    wc.hInstance = hInstance;
    wc.lpszClassName = L"MabinogiClientManagerClass";
    RegisterClassExW(&wc);
    g_hWnd = CreateWindowExW(0, L"MabinogiClientManagerClass", L"ClientManager", WS_OVERLAPPEDWINDOW, 0, 0, 0, 0, NULL, NULL, hInstance, NULL);

    g_iconNormal = (HICON)LoadImageW(hInstance, MAKEINTRESOURCEW(1), IMAGE_ICON, 32, 32, LR_DEFAULTCOLOR);
    if (g_iconNormal) {
        g_iconNormalOwned = true;
    } else {
        g_iconNormal = (HICON)LoadImageW(NULL, (ExeDir() + L"\\icon.ico").c_str(), IMAGE_ICON, 32, 32, LR_LOADFROMFILE);
        if (g_iconNormal) g_iconNormalOwned = true;
    }
    if (!g_iconNormal) g_iconNormal = LoadIconW(NULL, MAKEINTRESOURCEW(32512));
    g_iconBlue = CreateBlueIcon(g_iconNormal);

    ZeroMemory(&g_nid, sizeof(g_nid));
    g_nid.cbSize = sizeof(g_nid);
    g_nid.hWnd = g_hWnd;
    g_nid.uID = 1;
    g_nid.uFlags = NIF_ICON | NIF_MESSAGE | NIF_TIP;
    g_nid.uCallbackMessage = WM_TRAYICON;
    g_nid.hIcon = g_iconNormal;
    lstrcpynW(g_nid.szTip, L"Mabinogi Client Manager", 128);
    Shell_NotifyIconW(NIM_ADD, &g_nid);

    ResumeAllClients();   // 上次若被強制關閉，遊戲可能還停在暫停狀態
    InitialSync();
    SaveAllSettings();
    SetTimer(g_hWnd, 1, g_syncInterval, NULL);
    if (g_affReset) Notify(T(S_AFF_RESET));   // 設定檔的核心配置與這台電腦不同，已重設親和性

    g_hook1 = SetWinEventHook(EVENT_SYSTEM_FOREGROUND, EVENT_SYSTEM_FOREGROUND, NULL, WinEventProc, 0, 0, WINEVENT_OUTOFCONTEXT);
    g_hook2 = SetWinEventHook(EVENT_SYSTEM_MINIMIZESTART, EVENT_SYSTEM_MINIMIZEEND, NULL, WinEventProc, 0, 0, WINEVENT_OUTOFCONTEXT);
    g_hook3 = SetWinEventHook(EVENT_SYSTEM_MOVESIZESTART, EVENT_SYSTEM_MOVESIZEEND, NULL, WinEventProc, 0, 0, WINEVENT_OUTOFCONTEXT);
    g_hook4 = SetWinEventHook(EVENT_SYSTEM_MENUSTART, EVENT_SYSTEM_MENUPOPUPSTART, NULL, WinEventProc, 0, 0, WINEVENT_OUTOFCONTEXT);

    g_engine = std::thread(EngineThread);
    CreateOverlayWindow();
    StartMonitor();
    UpdateFpsSession();
    UpdateOverlayVisibility();

    MSG msg;
    while (GetMessageW(&msg, NULL, 0, 0) > 0) {
        TranslateMessage(&msg);
        DispatchMessageW(&msg);
    }

    StopMonitor();
    StopFps();
    if (g_ovHwnd) DestroyWindow(g_ovHwnd);
    ShutdownEngine();
    if (g_hook1) UnhookWinEvent(g_hook1);
    if (g_hook2) UnhookWinEvent(g_hook2);
    if (g_hook3) UnhookWinEvent(g_hook3);
    if (g_hook4) UnhookWinEvent(g_hook4);
    if (g_hookGame) UnhookWinEvent(g_hookGame);
    KillTimer(g_hWnd, 1);
    Shell_NotifyIconW(NIM_DELETE, &g_nid);
    if (g_iconBlue && g_iconBlue != g_iconNormal) DestroyIcon(g_iconBlue);
    if (g_iconNormalOwned && g_iconNormal) DestroyIcon(g_iconNormal);
    if (g_timer) CloseHandle(g_timer);
    if (g_wake) CloseHandle(g_wake);
    if (g_pauseAck) CloseHandle(g_pauseAck);
    if (g_monWake) CloseHandle(g_monWake);
    if (g_mutex) {
        ReleaseMutex(g_mutex);
        CloseHandle(g_mutex);
    }
    return 0;
}
