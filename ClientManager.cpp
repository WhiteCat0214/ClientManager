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
#include <shobjidl.h>
#include <objidl.h>
#include <commdlg.h>
#include <cmath>
#include <algorithm>
using std::min;   // gdiplus.h 內部使用不含 std:: 的 min / max (這裡定義了 NOMINMAX)
using std::max;
#include <gdiplus.h>
#include "version.h"

#pragma comment(lib, "user32.lib")
#pragma comment(lib, "gdiplus.lib")
#pragma comment(lib, "comdlg32.lib")
#pragma comment(lib, "gdi32.lib")
#pragma comment(lib, "shell32.lib")
#pragma comment(lib, "advapi32.lib")
#pragma comment(lib, "winmm.lib")
#pragma comment(lib, "pdh.lib")
#pragma comment(lib, "psapi.lib")
#pragma comment(lib, "dxgi.lib")
#pragma comment(lib, "iphlpapi.lib")
#pragma comment(lib, "comctl32.lib")
#pragma comment(lib, "ole32.lib")
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
    ID_RESTART_CLIENT, ID_RESTART_LAUNCHER, ID_TERM, ID_EXIT, ID_SETTINGS, ID_HIDE_TASKBAR, ID_MOUSE_CLIP,
    ID_RATIO_BASE = 1100,
    ID_PRIO_CPU_BASE = 1200,   // + 等級 1..6
    ID_GPU_BASE = 1240,        // + 等級 1..6
    ID_IO_BASE = 1260,         // + 等級 1..4
    ID_SHOWTIP = 1270,
    ID_AFF_ALL = 1290, ID_AFF_P, ID_AFF_PNOHT, ID_AFF_E,
    ID_AFFCORE_BASE = 1300,    // + 邏輯核心編號 0..63
    ID_DBL_BASE = 1450,        // + 連點兩下圖示的動作 0..4
    ID_LANG_BASE = 1400,       // + 語言 0..5 (自動 / 繁中 / 簡中 / 英文 / 日文 / 韓文)
    ID_OV_ENABLE = 1500,       // 效能監控：啟用 / 鎖定位置
    ID_OV_LOCK,
    ID_OV_LAST = 1599,
    ID_IMG_MASTER = 1600,      // 圖片置頂：總開關 / 全域鎖定 / 設定 / 各組啟用
    ID_IMG_LOCKALL,
    ID_IMG_SETTINGS,
    ID_IMG_GROUP_BASE = 1610,  // + 組別 0..9
    ID_IMG_LAST = 1699
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
static std::atomic<int> g_lang(1);               // 實際使用的語言 (1..5)

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
static bool g_monDlgOpen = false;                   // 設定視窗是否開啟中 (開啟期間，監控的位置與選項要等按下「確定」才寫入 ini)
static bool g_monPreview = false;                   // 設定視窗正顯示「效能監控」頁 (固定顯示監控畫面做預覽)
static HWND g_monDlgHwnd = NULL;
static void UpdateOverlayVisibility();
static void ImgUpdateVisibility();
static void ImgLoadSettings();
static void ImgSaveMissing();
static bool g_imgMaster = false;       // 圖片置頂總開關 (不改變各組的啟用設定)
static bool g_imgLockAll = false;      // 圖片置頂全域鎖定
static std::atomic<bool> g_ovLatency(true);         // 顯示網路延遲
static std::atomic<int> g_ovCpuMethod(0);           // CPU 使用率算法：0 = PDH 效能計數器 (預設)，1 = CPU 週期數，2 = 行程 CPU 時間
static std::atomic<int> g_ovLatMethod(0);           // Latency 取樣方式：0 = 最近一次樣本值 (預設)，1 = 平滑往返時間
static std::atomic<int> g_dblAction(0);             // 連點兩下圖示的動作：0 = 開啟設定頁面 (預設)，1 = 切換無邊框 / 還原，2 = 啟用 / 關閉 CPU 限制，3 = 啟用 / 關閉監控，4 = 隱藏 / 顯示遊戲工作列
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
static bool g_hideTaskbar = false;      // 隱藏遊戲在工作列上的按鈕 (只在 UI 執行緒讀寫)
static int g_lockStyle = 0;             // ini 的 LockStyle：0 = 鎖定時不改視窗樣式 (預設)，1 = 移除縮放邊框與最大化按鈕 (舊做法)
static ITaskbarList* g_taskbarList = NULL;
static ULONGLONG g_tbLastApply = 0;     // 上次套用的時間 (設成 0 = 下一次偵測時立刻重新套用)
static size_t g_tbSig = 0;              // 上次套用時的遊戲視窗組合
static bool g_mouseClip = false;        // 限制滑鼠移動範圍 (只在 UI 執行緒讀寫)
static bool g_mouseClipBorderless = false;   // ini 的 MouseClipBorderless：連「無邊框全視窗模式」也限制 (預設只限制全螢幕模式)
static int g_mouseClipMargin = 15;      // ini 的 MouseClipMargin：限制範圍距離遊戲畫面四邊的像素數 (沒有設定介面，直接改 ini)
static bool g_clipActive = false;       // 目前是否由本工具限制著滑鼠
static RECT g_clipRect = { 0, 0, 0, 0 };   // 本工具設定的限制範圍
static bool g_clipTimerOn = false;
static std::string g_clipDbg;           // 診斷：遊戲最後一次為前景時的判斷細節 (只在 UI 執行緒讀寫，顯示於「關於」)
static ULONGLONG g_clipDbgTick = 0;
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
//  多語系：繁體中文 / 簡體中文 / 英文 / 日文 / 韓文
// ---------------------------------------------------------------------------
enum UiLang { UL_AUTO = 0, UL_ZHTW = 1, UL_ZHCN = 2, UL_EN = 3, UL_JA = 4, UL_KO = 5 };
static const int kLangCount = 5;   // 可選的語言數 (不含自動)

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
    S_SET_TITLE,
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
    S_M_SETTINGS,
    S_ABOUT_TITLE,
    S_ABOUT_GROUP,
    S_ABOUT_TEXT,
    S_DLG_STOP_UPDATE,
    S_DLG_AUTO_UPDATE,
    S_M_HIDE_TASKBAR,
    S_M_MOUSE_CLIP,
    S_TIP_WINDOWED,
    S_TIP_FULLSCREEN,
    S_CAT_WINDOW,
    S_CAT_PRIO,
    S_CAT_CPU,
    S_CAT_OTHER,
    S_BORDERLESS,
    S_TOAST_ON,
    S_TOAST_OFF,
    S_DBL_SETTINGS,
    S_DBL_TASKBAR,
    S_G_WINDOW,
    S_G_MOUSE,
    S_G_PRIO,
    S_LOCKSTYLE,
    S_LOCKSTYLE_0,
    S_LOCKSTYLE_1,
    S_NOTE_WINDOWED,
    S_CLIP_MARGIN,
    S_CLIP_RANGE,
    S_CLIP_BL,
    S_PRIO_UNSET,
    S_M_EXIT,
    S_M_IMG,
    S_IMG_MASTER,
    S_IMG_GROUP,
    S_IMG_LOCKALL,
    S_IMG_SETTINGS,
    S_IMG_GROUPBOX,
    S_IMG_SEL,
    S_IMG_GROUPN,
    S_IMG_ENABLE,
    S_IMG_LOCK,
    S_IMG_NAME,
    S_IMG_SRC,
    S_IMG_SRC_W,
    S_IMG_SRC_B,
    S_IMG_SRC_C,
    S_IMG_SRC_F,
    S_IMG_PATH,
    S_IMG_BROWSE,
    S_IMG_OPACITY,
    S_IMG_SCALE,
    S_IMG_W,
    S_IMG_H,
    S_IMG_FLIP,
    S_IMG_ROT,
    S_IMG_Z,
    S_IMG_FGONLY,
    S_IMG_GIFPAUSE,
    S_IMG_GIFSPEED,
    S_IMG_RESETSIZE,
    S_IMG_NOTE,
    S_IMG_MISSING,
    S_IMG_MISSING2,
    S_IMG_NOTSET,
    S_IMG_LOADFAIL,
    S_IMG_FILTER,
    S__COUNT
};

static const wchar_t* const kStr[S__COUNT][5] = {
    { L"找不到執行中的遊戲 (Client.exe)！\n需先手動執行一次遊戲，才能使用此功能。", L"找不到正在运行的游戏 (Client.exe)！\n需要先手动运行一次游戏，才能使用此功能。", L"No running game (Client.exe) found!\nStart the game manually at least once before using this feature.", L"実行中のゲーム (Client.exe) が見つかりません。\nこの機能を使うには、先に一度ゲームを手動で起動してください。", L"실행 중인 게임 (Client.exe)을 찾을 수 없습니다!\n이 기능을 사용하려면 먼저 게임을 한 번 직접 실행해 주세요." },   // NO_GAME
    { L"找不到執行中的遊戲 (Client.exe)！\n需先手動執行一次遊戲，工具才能記住遊戲路徑。", L"找不到正在运行的游戏 (Client.exe)！\n需要先手动运行一次游戏，工具才能记住游戏路径。", L"No running game (Client.exe) found!\nStart the game manually once so the tool can remember its path.", L"実行中のゲーム (Client.exe) が見つかりません。\n一度ゲームを手動で起動して、パスを記憶させてください。", L"실행 중인 게임 (Client.exe)을 찾을 수 없습니다!\n도구가 게임 경로를 기억할 수 있도록 게임을 한 번 직접 실행해 주세요." },   // NO_GAME_PATH
    { L"找不到同目錄下的遊戲啟動器 (Mabinogi.exe)！\n需先手動執行遊戲一次，或確認遊戲資料夾是否完整。", L"找不到同目录下的游戏启动器 (Mabinogi.exe)！\n需要先手动运行一次游戏，或确认游戏文件夹是否完整。", L"Game launcher (Mabinogi.exe) not found in the same folder!\nStart the game manually once, or check that the game folder is intact.", L"同じフォルダーにゲームランチャー (Mabinogi.exe) が見つかりません。\n一度ゲームを手動で起動するか、ゲームフォルダーを確認してください。", L"같은 폴더에서 게임 런처 (Mabinogi.exe)를 찾을 수 없습니다!\n게임을 한 번 직접 실행하거나 게임 폴더가 온전한지 확인해 주세요." },   // NO_LAUNCHER
    { L"重啟遊戲失敗 (錯誤碼 %lu)", L"重启游戏失败 (错误码 %lu)", L"Failed to restart the game (error code %lu)", L"ゲームの再起動に失敗しました (エラーコード %lu)", L"게임 재시작에 실패했습니다 (오류 코드 %lu)" },   // RESTART_FAIL
    { L"至少需要選擇一個核心！", L"至少需要选择一个核心！", L"At least one core must be selected!", L"少なくとも 1 つのコアを選択してください。", L"코어를 하나 이상 선택해야 합니다!" },   // NEED_ONE_CORE
    { L"Mabinogi Client Manager 已經在背景執行中！", L"Mabinogi Client Manager 已经在后台运行！", L"Mabinogi Client Manager is already running in the background!", L"Mabinogi Client Manager は既にバックグラウンドで実行中です。", L"Mabinogi Client Manager가 이미 백그라운드에서 실행 중입니다!" },   // ALREADY_RUNNING
    { L"偵測到 CPU 核心配置與設定檔記錄的不同 (可能更換了電腦或 CPU)，\n已重設 CPU 親和性，將在遊戲啟動時重新讀取遊戲目前的設定。", L"检测到 CPU 核心配置与配置文件记录的不同 (可能更换了电脑或 CPU)，\n已重置 CPU 亲和性，将在游戏启动时重新读取游戏当前的设置。", L"The CPU core layout differs from the one saved in the settings file (the PC or CPU may have changed).\nCPU affinity has been reset and will be re-read from the game the next time it starts.", L"CPU のコア構成が設定ファイルの記録と異なります (PC または CPU が変更された可能性があります)。\nCPU アフィニティをリセットしました。次回ゲーム起動時に現在の設定を読み込みます。", L"CPU 코어 구성이 설정 파일에 기록된 것과 다릅니다 (PC 또는 CPU가 바뀌었을 수 있습니다).\nCPU 선호도(Affinity)를 초기화했으며, 다음에 게임이 시작될 때 게임의 현재 설정을 다시 읽어 옵니다." },   // AFF_RESET
    { L" (限制中)", L" (限制中)", L" (Limiting)", L" (制限中)", L" (제한 중)" },   // TIP_LIMITING
    { L"遊戲未執行", L"游戏未运行", L"Game not running", L"ゲーム未実行", L"게임 실행 안 됨" },   // TIP_NOGAME
    { L"目前的遊戲優先權 / 親和性", L"当前的游戏优先级 / 亲和性", L"Current game priority / affinity", L"現在のゲームの優先度 / アフィニティ", L"현재 게임 우선순위 / 선호도" },   // TIP_HEADER
    { L"CPU: %s", L"CPU: %s", L"CPU: %s", L"CPU: %s", L"CPU: %s" },   // TIP_CPU
    { L"GPU: %s", L"GPU: %s", L"GPU: %s", L"GPU: %s", L"GPU: %s" },   // TIP_GPU
    { L"I/O: %s", L"I/O: %s", L"I/O: %s", L"I/O: %s", L"I/O: %s" },   // TIP_IO
    { L"核心: %s", L"核心: %s", L"Cores: %s", L"コア: %s", L"코어: %s" },   // TIP_CORES
    { L"低 (Idle)", L"低 (Idle)", L"Idle", L"低 (Idle)", L"낮음 (Idle)" },   // PRIO_1
    { L"低於標準", L"低于标准", L"Below normal", L"通常以下", L"보통 이하" },   // PRIO_2
    { L"標準", L"标准", L"Normal", L"通常", L"보통" },   // PRIO_3
    { L"高於標準", L"高于标准", L"Above normal", L"通常以上", L"보통 이상" },   // PRIO_4
    { L"高", L"高", L"High", L"高", L"높음" },   // PRIO_5
    { L"即時 (Realtime)", L"实时 (Realtime)", L"Realtime", L"リアルタイム (Realtime)", L"실시간 (Realtime)" },   // PRIO_6
    { L"極低", L"极低", L"Very low", L"非常に低い", L"매우 낮음" },   // IO_1
    { L"低", L"低", L"Low", L"低", L"낮음" },   // IO_2
    { L"正常", L"正常", L"Normal", L"通常", L"보통" },   // IO_3
    { L"高", L"高", L"High", L"高", L"높음" },   // IO_4
    { L"切換無邊框 / 還原", L"切换无边框 / 还原", L"Toggle borderless / restore", L"ボーダーレス切替 / 元に戻す", L"테두리 없음 전환 / 복원" },   // M_TOGGLE
    { L"鎖定視窗大小及位置", L"锁定窗口大小及位置", L"Lock window size and position", L"ウィンドウのサイズと位置を固定", L"창 크기 및 위치 고정" },   // M_LOCK
    { L"重置視窗大小和位置", L"重置窗口大小和位置", L"Reset window size and position", L"ウィンドウのサイズと位置をリセット", L"창 크기 및 위치 초기화" },   // M_RESET
    { L"遊戲優先權 / 親和性", L"游戏优先级 / 亲和性", L"Game priority / affinity", L"ゲームの優先度 / アフィニティ", L"게임 우선순위 / 선호도" },   // M_GAMEPRIO
    { L"CPU優先權", L"CPU优先级", L"CPU priority", L"CPU 優先度", L"CPU 우선순위" },   // M_CPUPRIO
    { L"CPU親和性", L"CPU亲和性", L"CPU affinity", L"CPU アフィニティ", L"CPU 선호도" },   // M_CPUAFF
    { L"GPU優先權", L"GPU优先级", L"GPU priority", L"GPU 優先度", L"GPU 우선순위" },   // M_GPUPRIO
    { L"於工具提示顯示目前狀態", L"在工具提示中显示当前状态", L"Show current status in tooltip", L"ツールチップに現在の状態を表示", L"툴팁에 현재 상태 표시" },   // M_TIPSHOW
    { L"I/O優先權", L"I/O优先级", L"I/O priority", L"I/O 優先度", L"I/O 우선순위" },   // M_IOPRIO
    { L"全選", L"全选", L"Select all", L"すべて選択", L"모두 선택" },   // AFF_ALL
    { L"僅大核 (P-core)", L"仅大核 (P-core)", L"P-cores only", L"P コアのみ", L"P 코어만" },   // AFF_P
    { L"僅大核 (P-core) 不含%s", L"仅大核 (P-core) 不含%s", L"P-cores only (no %s)", L"P コアのみ (%s なし)", L"P 코어만 (%s 제외)" },   // AFF_PNOHT
    { L"僅實體核心 (不含%s)", L"仅物理核心 (不含%s)", L"Physical cores only (no %s)", L"物理コアのみ (%s なし)", L"물리 코어만 (%s 제외)" },   // AFF_NOHT
    { L"僅小核 (E-core)", L"仅小核 (E-core)", L"E-cores only", L"E コアのみ", L"E 코어만" },   // AFF_E
    { L"核心 %d %s", L"核心 %d %s", L"Core %d %s", L"コア %d %s", L"코어 %d %s" },   // CORE_ITEM
    { L"(大核 P-core)", L"(大核 P-core)", L"(P-core)", L"(P コア)", L"(P 코어)" },   // CORE_P
    { L"(大核 P-core) %s", L"(大核 P-core) %s", L"(P-core) %s", L"(P コア) %s", L"(P 코어) %s" },   // CORE_P_HT
    { L"(小核 E-core)", L"(小核 E-core)", L"(E-core)", L"(E コア)", L"(E 코어)" },   // CORE_E
    { L"(小核 E-core) %s", L"(小核 E-core) %s", L"(E-core) %s", L"(E コア) %s", L"(E 코어) %s" },   // CORE_E_HT
    { L"(實體核心)", L"(物理核心)", L"(Physical core)", L"(物理コア)", L"(물리 코어)" },   // CORE_PHYS
    { L"(%s)", L"(%s)", L"(%s)", L"(%s)", L"(%s)" },   // CORE_HT
    { L"超執行緒", L"超线程", L"Hyper-Threading", L"ハイパースレッディング", L"하이퍼스레딩" },   // SMT_INTEL
    { L"超執行緒", L"超线程", L"SMT", L"SMT", L"SMT" },   // SMT_OTHER
    { L"限制CPU使用率", L"限制CPU使用率", L"Limit CPU usage", L"CPU 使用率を制限", L"CPU 사용률 제한" },   // M_LIMIT
    { L"啟用CPU限制", L"启用CPU限制", L"Enable CPU limit", L"CPU 制限を有効にする", L"CPU 제한 사용" },   // M_ENABLE
    { L"限制時同時降低優先權 / 節能模式", L"限制时同时降低优先级 / 节能模式", L"Lower priority / efficiency mode while limiting", L"制限中は優先度を下げる / 省電力モード", L"제한 중 우선순위 낮춤 / 효율 모드" },   // M_ECO
    { L"生效條件", L"生效条件", L"When to apply", L"適用条件", L"적용 조건" },   // M_COND
    { L"永遠限制 CPU 使用率", L"始终限制 CPU 使用率", L"Always limit CPU usage", L"常に CPU 使用率を制限", L"항상 CPU 사용률 제한" },   // C_ALWAYS
    { L"僅在視窗最小化時生效", L"仅在窗口最小化时生效", L"Only when the window is minimized", L"ウィンドウ最小化時のみ", L"창이 최소화되었을 때만" },   // C_MIN
    { L"僅在視窗最小化或於背景執行時生效", L"仅在窗口最小化或在后台运行时生效", L"Only when minimized or in the background", L"最小化またはバックグラウンド時のみ", L"최소화되었거나 백그라운드일 때만" },   // C_BG
    { L"限制比例", L"限制比例", L"Limit ratio", L"制限割合", L"제한 비율" },   // M_RATIO
    { L"強制重啟 / 結束遊戲", L"强制重启 / 结束游戏", L"Force restart / quit game", L"ゲームの強制再起動 / 終了", L"게임 강제 재시작 / 종료" },   // M_RESTARTMENU
    { L"重啟遊戲 (Client.exe)", L"重启游戏 (Client.exe)", L"Restart game (Client.exe)", L"ゲームを再起動 (Client.exe)", L"게임 재시작 (Client.exe)" },   // M_RESTART_CLIENT
    { L"重啟遊戲 (Mabinogi.exe)", L"重启游戏 (Mabinogi.exe)", L"Restart game (Mabinogi.exe)", L"ゲームを再起動 (Mabinogi.exe)", L"게임 재시작 (Mabinogi.exe)" },   // M_RESTART_LAUNCHER
    { L"強制結束遊戲", L"强制结束游戏", L"Force quit game", L"ゲームを強制終了", L"게임 강제 종료" },   // M_TERM
    { L"語言", L"语言", L"Language", L"言語", L"언어" },   // M_LANG
    { L"自動選擇", L"自动选择", L"Auto", L"自動選択", L"자동 선택" },   // L_AUTO
    { L"(限制中)", L"(限制中)", L"(Limited)", L"(制限中)", L"(제한됨)" },   // OV_LIMITING
    { L"效能監控", L"性能监控", L"Performance monitor", L"パフォーマンスモニター", L"성능 모니터" },   // M_MON
    { L"啟用監控", L"启用监控", L"Enable monitor", L"モニターを有効にする", L"모니터 사용" },   // MON_ENABLE
    { L"顯示項目", L"显示项目", L"Items", L"表示項目", L"표시 항목" },   // MON_ITEMS
    { L"比例", L"比例", L"Percentage", L"割合", L"비율" },   // MON_PCT
    { L"實際值 (GHz)", L"实际值 (GHz)", L"Actual value (GHz)", L"実測値 (GHz)", L"실제 값 (GHz)" },   // MON_ACTUAL_GHZ
    { L"實際值 (MB)", L"实际值 (MB)", L"Actual value (MB)", L"実測値 (MB)", L"실제 값 (MB)" },   // MON_ACTUAL_MB
    { L"排列方式", L"排列方式", L"Layout", L"レイアウト", L"배치 방식" },   // MON_LAYOUT
    { L"直式 (每行一項)", L"竖式 (每行一项)", L"Vertical (one item per line)", L"縦 (1 行に 1 項目)", L"세로 (한 줄에 한 항목)" },   // MON_VERT
    { L"橫式 (以文字分隔)", L"横式 (以文字分隔)", L"Horizontal (separated by text)", L"横 (文字で区切る)", L"가로 (문자로 구분)" },   // MON_HORZ
    { L"鎖定位置 (滑鼠穿透)", L"锁定位置 (鼠标穿透)", L"Lock position (click-through)", L"位置を固定 (クリックを透過)", L"위치 고정 (클릭 통과)" },   // MON_LOCK
    { L"更新頻率", L"更新频率", L"Update interval", L"更新間隔", L"갱신 주기" },   // MON_INTERVAL
    { L"外觀", L"外观", L"Appearance", L"外観", L"모양" },   // MON_STYLE
    { L"字體大小", L"字体大小", L"Font size", L"フォントサイズ", L"글꼴 크기" },   // MON_FONTSIZE
    { L"不透明度", L"不透明度", L"Opacity", L"不透明度", L"불투명도" },   // MON_OPACITY
    { L"鎖定時無背景", L"锁定时无背景", L"No background when locked", L"固定時は背景なし", L"고정 시 배경 없음" },   // MON_LOCKNOBG
    { L"重置位置", L"重置位置", L"Reset position", L"位置をリセット", L"위치 초기화" },   // MON_RESETPOS
    { L"色碼格式不正確，請輸入 6 位數的 HEX (0-9、A-F)。", L"色码格式不正确，请输入 6 位 HEX (0-9、A-F)。", L"Invalid color code. Enter 6 hex digits (0-9, A-F).", L"カラーコードの形式が正しくありません。16 進数 6 桁 (0-9, A-F) で入力してください。", L"색상 코드 형식이 올바르지 않습니다. 6자리 HEX (0-9, A-F)를 입력해 주세요." },   // DLG_COLOR_BAD
    { L"確定", L"确定", L"OK", L"OK", L"확인" },   // DLG_OK
    { L"取消", L"取消", L"Cancel", L"キャンセル", L"취소" },   // DLG_CANCEL
    { L"設定", L"设置", L"Settings", L"設定", L"설정" },   // SET_TITLE
    { L"套用", L"应用", L"Apply", L"適用", L"적용" },   // DLG_APPLY
    { L"字體顏色", L"字体颜色", L"Text color", L"文字の色", L"글꼴 색" },   // LBL_TEXTCOLOR
    { L"文字外框顏色", L"文字外框颜色", L"Text outline color", L"文字の縁取りの色", L"글자 외곽선 색" },   // LBL_OUTLINECOLOR
    { L"背景顏色", L"背景颜色", L"Background color", L"背景色", L"배경색" },   // LBL_BGCOLOR
    { L"只在遊戲前景時顯示 (僅在設定視窗關閉後生效)", L"仅在游戏前台时显示 (仅在设置窗口关闭后生效)", L"Show only when the game is in the foreground (takes effect after this window is closed)", L"ゲームが前面のときのみ表示 (この画面を閉じた後に有効)", L"게임이 전면일 때만 표시 (이 창을 닫은 후 적용)" },   // MON_FGONLY_DLG
    { L"每 0.5 秒", L"每 0.5 秒", L"Every 0.5 s", L"0.5 秒ごと", L"0.5초마다" },   // MON_EVERY_05
    { L"每 1 秒", L"每 1 秒", L"Every 1 s", L"1 秒ごと", L"1초마다" },   // MON_EVERY_1
    { L"每 2 秒", L"每 2 秒", L"Every 2 s", L"2 秒ごと", L"2초마다" },   // MON_EVERY_2
    { L"連點兩下圖示的動作", L"双击图标的动作", L"Double-click action", L"ダブルクリックの動作", L"아이콘 두 번 클릭 동작" },   // M_DBLCLICK
    { L"啟用CPU限制 / 關閉CPU限制", L"启用CPU限制 / 关闭CPU限制", L"Enable / disable CPU limit", L"CPU 制限の有効 / 無効を切り替え", L"CPU 제한 켜기 / 끄기" },   // DBL_CPU
    { L"啟用監控 / 關閉監控", L"启用监控 / 关闭监控", L"Enable / disable monitor", L"モニターの有効 / 無効を切り替え", L"모니터 켜기 / 끄기" },   // DBL_MON
    { L"重啟 Client.exe", L"重启 Client.exe", L"Restart Client.exe", L"Client.exe を再起動", L"Client.exe 재시작" },   // DLG_RESTART_CLIENT
    { L"重啟 Mabinogi.exe", L"重启 Mabinogi.exe", L"Restart Mabinogi.exe", L"Mabinogi.exe を再起動", L"Mabinogi.exe 재시작" },   // DLG_RESTART_LAUNCHER
    { L"關閉", L"关闭", L"Close", L"閉じる", L"닫기" },   // DLG_CLOSE
    { L"顯示設定", L"显示设置", L"Display settings", L"表示設定", L"표시 설정" },   // MON_DISPLAY
    { L"分隔文字", L"分隔文字", L"Separator", L"区切り文字", L"구분 문자" },   // MON_SEPARATOR
    { L"顯示順序 (拖曳排序)", L"显示顺序 (拖动排序)", L"Order (drag to sort)", L"表示順序 (ドラッグ)", L"표시 순서 (끌어서 정렬)" },   // MON_ORDER
    { L"CPU 使用率算法", L"CPU 使用率算法", L"CPU usage method", L"CPU 使用率の算出方法", L"CPU 사용률 계산 방식" },   // MON_METHOD
    { L"週期法 (CPU 週期數)", L"周期法 (CPU 周期数)", L"Cycle count", L"サイクル数", L"주기 방식 (CPU 사이클 수)" },   // METHOD_CYC
    { L"時間法 (行程 CPU 時間)", L"时间法 (进程 CPU 时间)", L"Process CPU time", L"プロセス CPU 時間", L"시간 방식 (프로세스 CPU 시간)" },   // METHOD_TIME
    { L"診斷記錄", L"诊断记录", L"Diagnostic log", L"診断ログ", L"진단 기록" },   // MON_DEBUG
    { L"複製", L"复制", L"Copy", L"コピー", L"복사" },   // DLG_COPY
    { L"Latency 取樣方式", L"Latency 取样方式", L"Latency sampling", L"Latency の取得方法", L"Latency 샘플링 방식" },   // MON_LATMETHOD
    { L"最近一次樣本值 (預設)", L"最近一次样本值 (默认)", L"Latest sample (default)", L"最新のサンプル値 (既定)", L"최근 샘플 값 (기본값)" },   // LAT_SAMPLE
    { L"平滑往返時間", L"平滑往返时间", L"Smoothed round-trip time", L"平滑化した往復時間", L"평활화된 왕복 시간" },   // LAT_SMOOTH
    { L"估算 (行程時間 × 系統 Utility/Time)", L"估算 (进程时间 × 系统 Utility/Time)", L"Estimate (process time x system utility/time)", L"推定 (プロセス時間 × システム Utility/Time)", L"추정 (프로세스 시간 × 시스템 Utility/Time)" },   // METHOD_EST
    { L"設定...", L"设置...", L"Settings...", L"設定...", L"설정..." },   // M_SETTINGS
    { L"關於", L"关于", L"About", L"バージョン情報", L"정보" },   // ABOUT_TITLE
    { L"程式說明", L"程序说明", L"Description", L"プログラムの説明", L"프로그램 설명" },   // ABOUT_GROUP
    { L"瑪奇 (Mabinogi) Client.exe 的常駐管理工具 (顯示於通知區域)\n\n【主要功能說明】\n  ．視窗無邊框 / 鎖定大小位置 / 還原 (類似 Kisara 的偽全屏)\n  ．限制CPU使用率 (類似 BES, Battle Encoder Shirase 的CPU限制軟體)\n  ．優先權與親和性設定 (類似 Process Lasso 的程式優先權及CPU親和性的調整)\n  ．效能監控 (類似 XBOX Gamebar 的效能監控，另外加上資源監視器的網路TCP連線延遲資訊)",
      L"玛奇 (Mabinogi) Client.exe 的常驻管理工具 (显示于通知区域)\n\n【主要功能说明】\n  ．窗口无边框 / 锁定大小位置 / 还原 (类似 Kisara 的伪全屏)\n  ．限制CPU使用率 (类似 BES, Battle Encoder Shirase 的CPU限制软件)\n  ．优先级与亲和性设置 (类似 Process Lasso 的程序优先级及CPU亲和性的调整)\n  ．性能监控 (类似 XBOX Game Bar 的性能监控，另外加上资源监视器的网络TCP连接延迟信息)",
      L"A resident manager for Mabinogi's Client.exe (shown in the notification area)\n\n[Main features]\n  - Borderless window / lock size and position / restore (like Kisara's pseudo fullscreen)\n  - CPU usage limiting (like BES, Battle Encoder Shirase)\n  - Priority and affinity settings (like Process Lasso)\n  - Performance monitor (like the Xbox Game Bar, plus the TCP connection latency from Resource Monitor)",
      L"マビノギ (Mabinogi) Client.exe の常駐管理ツール (通知領域に表示)\n\n【主な機能】\n  ・ウィンドウのボーダーレス化 / サイズと位置のロック / 元に戻す (Kisara の疑似フルスクリーンに類似)\n  ・CPU 使用率の制限 (BES, Battle Encoder Shirase に類似)\n  ・優先度とアフィニティの設定 (Process Lasso に類似)\n  ・パフォーマンス モニター (Xbox Game Bar に類似、リソース モニターの TCP 接続遅延情報も追加)", L"마비노기 (Mabinogi) Client.exe 상주 관리 도구 (알림 영역에 표시)\n\n[주요 기능]\n  - 창 테두리 없애기 / 크기·위치 고정 / 복원 (Kisara의 의사 전체 화면과 유사)\n  - CPU 사용률 제한 (BES, Battle Encoder Shirase와 유사)\n  - 우선순위 및 선호도 설정 (Process Lasso와 유사)\n  - 성능 모니터 (Xbox Game Bar와 유사하며, 리소스 모니터의 TCP 연결 지연 정보를 추가)" },   // ABOUT_TEXT
    { L"停止更新", L"停止更新", L"Stop updating", L"更新を停止", L"갱신 중지" },   // DLG_STOP_UPDATE
    { L"自動更新", L"自动更新", L"Auto update", L"自動更新", L"자동 갱신" },   // DLG_AUTO_UPDATE
    { L"隱藏遊戲工作列", L"隐藏游戏任务栏", L"Hide game taskbar button", L"ゲームのタスクバー ボタンを隠す", L"게임 작업 표시줄 버튼 숨기기" },   // M_HIDE_TASKBAR
    { L"限制滑鼠移動範圍", L"限制鼠标移动范围", L"Restrict mouse movement area", L"マウスの移動範囲を制限", L"마우스 이동 범위 제한" },   // M_MOUSE_CLIP
    { L"這項功能僅在視窗模式下生效", L"该功能仅在窗口模式下生效", L"This feature only works in windowed mode", L"この機能はウィンドウモードでのみ有効です", L"이 기능은 창 모드에서만 작동합니다" },   // TIP_WINDOWED
    { L"這項功能僅在全螢幕模式下生效", L"该功能仅在全屏模式下生效", L"This feature only works in fullscreen mode", L"この機能はフルスクリーンモードでのみ有効です", L"이 기능은 전체 화면 모드에서만 작동합니다" },   // TIP_FULLSCREEN
    { L"遊戲視窗", L"游戏窗口", L"Game window", L"ゲームウィンドウ", L"게임 창" },   // CAT_WINDOW
    { L"優先權 / 親和性", L"优先级 / 亲和性", L"Priority / affinity", L"優先度 / アフィニティ", L"우선순위 / 선호도" },   // CAT_PRIO
    { L"CPU限制", L"CPU限制", L"CPU limit", L"CPU 制限", L"CPU 제한" },   // CAT_CPU
    { L"其他", L"其他", L"Other", L"その他", L"기타" },   // CAT_OTHER
    { L"無邊框", L"无边框", L"Borderless", L"ボーダーレス", L"테두리 없음" },   // BORDERLESS
    { L"%s：已啟用", L"%s：已启用", L"%s: Enabled", L"%s：有効", L"%s: 켜짐" },   // TOAST_ON
    { L"%s：已關閉", L"%s：已关闭", L"%s: Disabled", L"%s：無効", L"%s: 꺼짐" },   // TOAST_OFF
    { L"開啟設定頁面", L"打开设置页面", L"Open settings", L"設定を開く", L"설정 열기" },   // DBL_SETTINGS
    { L"隱藏 / 顯示遊戲工作列", L"隐藏 / 显示游戏任务栏", L"Hide / show game taskbar button", L"ゲームのタスクバー ボタンの非表示 / 表示", L"게임 작업 표시줄 버튼 숨기기 / 표시" },   // DBL_TASKBAR
    { L"視窗", L"窗口", L"Window", L"ウィンドウ", L"창" },   // G_WINDOW
    { L"滑鼠", L"鼠标", L"Mouse", L"マウス", L"마우스" },   // G_MOUSE
    { L"優先權", L"优先级", L"Priority", L"優先度", L"우선순위" },   // G_PRIO
    { L"鎖定方式", L"锁定方式", L"Lock method", L"固定方法", L"잠금 방식" },   // LOCKSTYLE
    { L"不改變視窗樣式 (預設)", L"不改变窗口样式 (默认)", L"Keep the window style (default)", L"ウィンドウのスタイルを変更しない (既定)", L"창 스타일 유지 (기본값)" },   // LOCKSTYLE_0
    { L"移除縮放邊框與最大化按鈕", L"移除缩放边框与最大化按钮", L"Remove the sizing border and maximize button", L"サイズ変更枠と最大化ボタンを削除", L"크기 조절 테두리와 최대화 버튼 제거" },   // LOCKSTYLE_1
    { L"「無邊框」「鎖定」「重置」只在遊戲顯示器模式為「視窗模式」時生效。", L"「无边框」「锁定」「重置」仅在游戏显示器模式为「窗口模式」时生效。", L"Borderless, lock and reset only work while the game's display mode is windowed mode.", L"「ボーダーレス」「固定」「リセット」は、ゲームの表示モードが「ウィンドウモード」のときのみ有効です。", L"'테두리 없음', '잠금', '초기화'는 게임의 디스플레이 모드가 '창 모드'일 때만 작동합니다." },   // NOTE_WINDOWED
    { L"邊界寬度 (像素)", L"边界宽度 (像素)", L"Margin width (pixels)", L"余白の幅 (ピクセル)", L"경계 너비 (픽셀)" },   // CLIP_MARGIN
    { L"(0 ~ 200)", L"(0 ~ 200)", L"(0 ~ 200)", L"(0 ~ 200)", L"(0 ~ 200)" },   // CLIP_RANGE
    { L"也套用於「無邊框全視窗模式」", L"也应用于「无边框全窗口模式」", L"Also apply in borderless full-window mode", L"「ボーダーレス全画面ウィンドウモード」にも適用", L"'테두리 없는 전체 창 모드'에도 적용" },   // CLIP_BL
    { L"(尚未設定)", L"(尚未设置)", L"(not set)", L"(未設定)", L"(설정 안 됨)" },   // PRIO_UNSET
    { L"結束程式", L"退出程序", L"Exit", L"終了", L"종료" },   // M_EXIT
    { L"圖片置頂", L"图片置顶", L"Pinned images", L"画像の最前面表示", L"이미지 항상 위에" },   // M_IMG
    { L"啟用圖片置頂 (全域啟用)", L"启用图片置顶 (全局启用)", L"Enable pinned images (global)", L"画像の最前面表示を有効にする (全体)", L"이미지 항상 위에 사용 (전체)" },   // IMG_MASTER
    { L"啟用第%d組", L"启用第%d组", L"Enable group %d", L"グループ %d を有効にする", L"그룹 %d 사용" },   // IMG_GROUP
    { L"鎖定全部圖片 (全域鎖定)", L"锁定全部图片 (全局锁定)", L"Lock all images (global lock)", L"すべての画像を固定 (全体固定)", L"모든 이미지 고정 (전체 고정)" },   // IMG_LOCKALL
    { L"圖片置頂設定...", L"图片置顶设置...", L"Pinned image settings...", L"画像の最前面表示の設定...", L"이미지 항상 위에 설정..." },   // IMG_SETTINGS
    { L"圖片組設定", L"图片组设置", L"Image group settings", L"画像グループの設定", L"이미지 그룹 설정" },   // IMG_GROUPBOX
    { L"選擇組別", L"选择组别", L"Group", L"グループ選択", L"그룹 선택" },   // IMG_SEL
    { L"第 %d 組", L"第 %d 组", L"Group %d", L"グループ %d", L"그룹 %d" },   // IMG_GROUPN
    { L"啟用此組", L"启用此组", L"Enable", L"有効", L"사용" },   // IMG_ENABLE
    { L"鎖定此組", L"锁定此组", L"Lock", L"固定", L"고정" },   // IMG_LOCK
    { L"名稱", L"名称", L"Name", L"名前", L"이름" },   // IMG_NAME
    { L"圖片來源", L"图片来源", L"Source", L"画像の種類", L"이미지 소스" },   // IMG_SRC
    { L"內建料理尺 (白色)", L"内置料理尺 (白色)", L"Built-in cooking ruler (white)", L"内蔵の料理定規 (白)", L"내장 요리 자 (흰색)" },   // IMG_SRC_W
    { L"內建料理尺 (黑色)", L"内置料理尺 (黑色)", L"Built-in cooking ruler (black)", L"内蔵の料理定規 (黒)", L"내장 요리 자 (검정)" },   // IMG_SRC_B
    { L"內建料理尺 (自訂顏色)", L"内置料理尺 (自定义颜色)", L"Built-in cooking ruler (custom color)", L"内蔵の料理定規 (カスタム色)", L"내장 요리 자 (사용자 색상)" },   // IMG_SRC_C
    { L"自選圖片 (jpg / png / gif)", L"自选图片 (jpg / png / gif)", L"Custom image (jpg / png / gif)", L"画像ファイル (jpg / png / gif)", L"사용자 이미지 (jpg / png / gif)" },   // IMG_SRC_F
    { L"路徑", L"路径", L"Path", L"パス", L"경로" },   // IMG_PATH
    { L"瀏覽...", L"浏览...", L"Browse...", L"参照...", L"찾아보기..." },   // IMG_BROWSE
    { L"不透明度 (%)", L"不透明度 (%)", L"Opacity (%)", L"不透明度 (%)", L"불투명도 (%)" },   // IMG_OPACITY
    { L"縮放比例 (%)", L"缩放比例 (%)", L"Scale (%)", L"拡大率 (%)", L"배율 (%)" },   // IMG_SCALE
    { L"寬", L"宽", L"W", L"幅", L"너비" },   // IMG_W
    { L"高", L"高", L"H", L"高さ", L"높이" },   // IMG_H
    { L"水平翻轉", L"水平翻转", L"Flip horizontally", L"左右反転", L"좌우 반전" },   // IMG_FLIP
    { L"旋轉", L"旋转", L"Rotate", L"回転", L"회전" },   // IMG_ROT
    { L"層級 (數字越大越上層)", L"层级 (数字越大越靠上)", L"Layer (higher = on top)", L"重なり順 (大きいほど上)", L"레이어 (클수록 위)" },   // IMG_Z
    { L"僅在遊戲視窗為前景時顯示", L"仅在游戏窗口为前台时显示", L"Show only when the game window is in the foreground", L"ゲームウィンドウが前面のときのみ表示", L"게임 창이 전면일 때만 표시" },   // IMG_FGONLY
    { L"暫停 GIF 動畫", L"暂停 GIF 动画", L"Pause GIF animation", L"GIF アニメを一時停止", L"GIF 애니메이션 일시 정지" },   // IMG_GIFPAUSE
    { L"GIF 播放速度", L"GIF 播放速度", L"GIF speed", L"GIF の再生速度", L"GIF 재생 속도" },   // IMG_GIFSPEED
    { L"重置為原始大小", L"重置为原始大小", L"Reset to original size", L"元のサイズに戻す", L"원래 크기로 초기화" },   // IMG_RESETSIZE
    { L"未鎖定時：拖曳圖片可移動，拖曳四角的控制點可等比例縮放，點一下圖片後可用方向鍵微調 1 像素 (按住 Shift 為 10 像素)。位置以所在螢幕的左上角起算。\n此頁的變更會立即生效並儲存，不需按「確定」。", L"未锁定时：拖动图片可移动，拖动四角的控制点可等比例缩放，点一下图片后可用方向键微调 1 像素 (按住 Shift 为 10 像素)。位置以所在屏幕的左上角起算。\n此页的更改会立即生效并保存，无需点击「确定」。", L"While unlocked: drag the image to move it, drag a corner handle to resize it proportionally, and click the image then use the arrow keys to nudge it 1 px (Shift = 10 px). Positions are measured from the top-left of the screen the image is on.\nChanges on this page apply and are saved immediately; OK is not needed.", L"固定していないとき：画像をドラッグして移動、四隅のハンドルをドラッグして縦横比を保ったまま拡大縮小、画像をクリックしてから矢印キーで 1 ピクセル単位で微調整できます (Shift で 10 ピクセル)。位置は画像があるモニターの左上が基準です。\nこのページの変更は即時に反映・保存され、「OK」は不要です。", L"고정하지 않았을 때: 이미지를 끌어 이동하고, 모서리 핸들을 끌어 비율을 유지한 채 크기를 조절하며, 이미지를 클릭한 뒤 방향키로 1픽셀씩 미세 조정할 수 있습니다 (Shift = 10픽셀). 위치는 이미지가 있는 모니터의 왼쪽 위 기준입니다.\n이 페이지의 변경 사항은 즉시 적용·저장되며 '확인'이 필요 없습니다." },   // IMG_NOTE
    { L"圖片遺失：%s", L"图片丢失：%s", L"Image missing: %s", L"画像が見つかりません：%s", L"이미지를 찾을 수 없음: %s" },   // IMG_MISSING
    { L"請在設定中重新指定圖片", L"请在设置中重新指定图片", L"Please choose the image again in Settings", L"設定で画像を指定し直してください", L"설정에서 이미지를 다시 지정하세요" },   // IMG_MISSING2
    { L"尚未選擇圖片", L"尚未选择图片", L"No image selected", L"画像が未選択です", L"이미지가 선택되지 않음" },   // IMG_NOTSET
    { L"第 %d 組的圖片無法載入：\n%s\n請到「設定」的「圖片置頂」頁重新指定圖片。", L"第 %d 组的图片无法加载：\n%s\n请到「设置」的「图片置顶」页重新指定图片。", L"The image of group %d could not be loaded:\n%s\nPlease choose it again on the Pinned images page in Settings.", L"グループ %d の画像を読み込めませんでした：\n%s\n「設定」の「画像の最前面表示」ページで指定し直してください。", L"그룹 %d의 이미지를 불러올 수 없습니다:\n%s\n'설정'의 '이미지 항상 위에' 페이지에서 다시 지정하세요." },   // IMG_LOADFAIL
    { L"圖片檔 (jpg / png / gif)", L"图片文件 (jpg / png / gif)", L"Image files (jpg / png / gif)", L"画像ファイル (jpg / png / gif)", L"이미지 파일 (jpg / png / gif)" },   // IMG_FILTER
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
    if (p == LANG_KOREAN) return UL_KO;
    return UL_EN;
}

// 優先讀設定檔的語言；設定為「自動」(或沒有設定) 時依系統語系
static void ApplyLanguage() {
    int sel = g_langSetting;
    g_lang = (sel >= UL_ZHTW && sel <= UL_KO) ? sel : DetectSystemLang();
}

static const wchar_t* LangName(int l) {
    switch (l) {
    case UL_ZHTW: return L"zh-TW";
    case UL_ZHCN: return L"zh-CN";
    case UL_EN: return L"en";
    case UL_JA: return L"ja";
    case UL_KO: return L"ko";
    }
    return L"auto";
}

static const wchar_t* LangLabel(int l) {
    switch (l) {
    case UL_ZHTW: return L"繁體中文 Chinese Traditional";
    case UL_ZHCN: return L"简体中文 Chinese Simplified";
    case UL_EN: return L"英文 English";
    case UL_JA: return L"日本語 Japanese";
    case UL_KO: return L"한국어 Korean";
    }
    return L"";
}

static int LangFromName(const wchar_t* n) {
    if (_wcsicmp(n, L"zh-TW") == 0) return UL_ZHTW;
    if (_wcsicmp(n, L"zh-CN") == 0) return UL_ZHCN;
    if (_wcsicmp(n, L"en") == 0) return UL_EN;
    if (_wcsicmp(n, L"ja") == 0) return UL_JA;
    if (_wcsicmp(n, L"ko") == 0) return UL_KO;
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

// 官方網頁登入器啟動遊戲時帶入的參數：/N:、/V: 是臨時的登入帳號密碼，/T: 是橘子的標誌 (通常是 /T:gamania)。
// 這三種參數 (連同值) 都不儲存到設定檔，重啟遊戲時也不帶入；其他參數維持原樣
static std::wstring StripLoginArgs(const std::wstring& args) {
    std::wstring out;
    size_t i = 0, n = args.size();
    while (i < n) {
        while (i < n && (args[i] == L' ' || args[i] == L'\t')) ++i;
        if (i >= n) break;
        size_t start = i;
        bool inQuote = false;
        while (i < n && (inQuote || (args[i] != L' ' && args[i] != L'\t'))) {
            if (args[i] == L'"') inQuote = !inQuote;
            ++i;
        }
        std::wstring tok = args.substr(start, i - start);
        size_t b = (!tok.empty() && tok[0] == L'"') ? 1 : 0;   // 整個參數被引號包起來的情況
        bool drop = tok.size() >= b + 3 && tok[b] == L'/' && tok[b + 2] == L':' &&
                    (tok[b + 1] == L'N' || tok[b + 1] == L'n' || tok[b + 1] == L'V' || tok[b + 1] == L'v' || tok[b + 1] == L'T' || tok[b + 1] == L't');
        if (drop) continue;
        if (!out.empty()) out += L' ';
        out += tok;
    }
    return out;
}

// 更新「最後一次的路徑與參數」；有變動才寫入設定檔
static void UpdateClientCache(const std::wstring& path, const std::wstring& argsIn) {
    const std::wstring args = StripLoginArgs(argsIn);
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
    g_dblAction = IniInt(L"DoubleClick", 0, 0, 4);
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
    SaveInt(L"HideTaskbar", g_hideTaskbar ? 1 : 0);
    SaveInt(L"MouseClip", g_mouseClip ? 1 : 0);
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
    SaveInt(L"MouseClipMargin", g_mouseClipMargin);
    SaveInt(L"MouseClipBorderless", g_mouseClipBorderless ? 1 : 0);
    SaveInt(L"LockStyle", g_lockStyle);
    SaveString(L"ClientPath", GetCachedPath());
    SaveString(L"ClientArgs", GetCachedArgs());
    SaveOverlaySettings();
    SaveInt(L"ImgMaster", g_imgMaster ? 1 : 0);
    SaveInt(L"ImgLockAll", g_imgLockAll ? 1 : 0);
    ImgSaveMissing();
}

// ini 的 MouseClipMargin：預設 15，範圍 0 ~ 200。每次啟動與每次從選單開啟「限制滑鼠移動範圍」時重新讀取
static void LoadMouseClipMargin() {
    int v = (int)GetPrivateProfileIntW(L"Settings", L"MouseClipMargin", 15, g_iniPath.c_str());
    g_mouseClipMargin = std::max(0, std::min(200, v));
    g_mouseClipBorderless = (GetPrivateProfileIntW(L"Settings", L"MouseClipBorderless", 0, g_iniPath.c_str()) != 0);
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
    g_hideTaskbar = (GetPrivateProfileIntW(L"Settings", L"HideTaskbar", 0, g_iniPath.c_str()) != 0);
    g_mouseClip = (GetPrivateProfileIntW(L"Settings", L"MouseClip", 0, g_iniPath.c_str()) != 0);
    g_lockStyle = (GetPrivateProfileIntW(L"Settings", L"LockStyle", 0, g_iniPath.c_str()) != 0) ? 1 : 0;
    LoadMouseClipMargin();
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
    ImgLoadSettings();
    buf[0] = 0;
    GetPrivateProfileStringW(L"Settings", L"ClientArgs", L"", buf.data(), (DWORD)buf.size(), g_iniPath.c_str());
    {
        std::wstring raw = buf.data();
        std::wstring clean = StripLoginArgs(raw);
        {
            std::lock_guard<std::mutex> lk(g_pathMtx);
            g_cachedArgs = clean;
        }
        if (clean != raw) SaveString(L"ClientArgs", clean);   // 設定檔裡若已有登入參數，立刻清除
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

// 開啟網址：本工具是管理員權限，直接開瀏覽器會讓瀏覽器也以管理員身分執行，
// 所以優先以一般權限由 explorer 開啟 (交給使用者的預設瀏覽器)，失敗時才退回一般的 ShellExecute
static void OpenUrl(const wchar_t* url) {
    wchar_t win[MAX_PATH];
    UINT n = GetWindowsDirectoryW(win, MAX_PATH);
    if (n > 0 && n < MAX_PATH) {
        std::wstring dir = win;
        DWORD err = 0;
        if (LaunchProcess(dir + L"\\explorer.exe", L"\"" + std::wstring(url) + L"\"", dir, true, &err)) return;
    }
    ShellExecuteW(NULL, L"open", url, NULL, NULL, SW_SHOWNORMAL);
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
                    ci.args = StripLoginArgs(ArgsFromCmdline(cmd));
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

struct WinState { RECT client; bool hasClient; bool managed; int stable; RECT last; bool lockDone; ULONGLONG enforceUntil; bool ours; };   // ours：目前的無邊框是本工具套用的
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
    // 只記錄視窗模式 (有標題列) 的大小與位置：全螢幕或無邊框狀態的大小不能當成「原本的視窗大小」
    if (IsIconic(h) || IsZoomed(h) || !HasCaption(h)) return;
    RECT c;
    POINT p;
    p.x = 0;
    p.y = 0;
    GetClientRect(h, &c);
    ClientToScreen(h, &p);
    MONITORINFO mi;
    ZeroMemory(&mi, sizeof(mi));
    mi.cbSize = sizeof(mi);
    if (GetMonitorInfoW(MonitorFromWindow(h, MONITOR_DEFAULTTONEAREST), &mi) &&
        c.right >= mi.rcMonitor.right - mi.rcMonitor.left && c.bottom >= mi.rcMonitor.bottom - mi.rcMonitor.top) return;   // 客戶區涵蓋整個螢幕 (全螢幕切換中的過渡大小)
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
    if (!sm) return;
    UINT f = MF_BYCOMMAND | (enabled ? MF_ENABLED : MF_GRAYED);
    EnableMenuItem(sm, SC_MOVE, f);
    if (g_lockStyle == 0) {   // 不改視窗樣式的鎖定：「大小」「最大化」也一起變灰
        EnableMenuItem(sm, SC_SIZE, f);
        EnableMenuItem(sm, SC_MAXIMIZE, f);
    }
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
    if (g_lockStyle == 1) {       // 舊做法：移除縮放邊框與最大化按鈕 (部分情況下遊戲自己切換顯示器模式會沒有反應)
        LONG_PTR s = GetWindowLongPtrW(h, GWL_STYLE);
        if (lock) s &= ~(LONG_PTR)(WS_THICKFRAME | WS_MAXIMIZEBOX);
        else s |= (LONG_PTR)(WS_THICKFRAME | WS_MAXIMIZEBOX);
        SetStyleKeepClient(h, s);
    }
    if (lock) {
        UpdateLockPos(h);
        SetMoveMenu(h, false);
    } else {
        g_lockPos.erase(h);
        SetMoveMenu(h, true);
    }
}

// ---------------------------------------------------------------------------
//  遊戲的三種顯示器模式：視窗模式 / 全螢幕模式 / 無邊框全視窗模式
//  本工具的無邊框 / 鎖定 / 重置只在「視窗模式」(有標題列) 運作，以及「本工具自己套用的無邊框」(可以還原回視窗模式)；
//  遊戲自己的全螢幕模式與無邊框全視窗模式 (沒有標題列、涵蓋整個螢幕、不是本工具套用的) 一律不去動
// ---------------------------------------------------------------------------
static bool RectCoversMonitor(HWND h) {
    MONITORINFO mi;
    ZeroMemory(&mi, sizeof(mi));
    mi.cbSize = sizeof(mi);
    RECT wr;
    if (!GetMonitorInfoW(MonitorFromWindow(h, MONITOR_DEFAULTTONEAREST), &mi) || !GetWindowRect(h, &wr)) return false;
    return wr.left <= mi.rcMonitor.left && wr.top <= mi.rcMonitor.top && wr.right >= mi.rcMonitor.right && wr.bottom >= mi.rcMonitor.bottom;
}

static bool RectIsWorkArea(HWND h) {
    MONITORINFO mi;
    ZeroMemory(&mi, sizeof(mi));
    mi.cbSize = sizeof(mi);
    RECT wr;
    if (!GetMonitorInfoW(MonitorFromWindow(h, MONITOR_DEFAULTTONEAREST), &mi) || !GetWindowRect(h, &wr)) return false;
    return EqualRect(&wr, &mi.rcWork) != 0;
}

// 本工具套用的無邊框是否還維持著：回到視窗模式 (有標題列)，或遊戲自己切成全螢幕 / 無邊框全視窗 (涵蓋整個螢幕而且不是工作區大小) 時就放手
static void UpdateOursFlag(HWND h, WinState& ws) {
    if (!ws.ours) return;
    if (HasCaption(h)) {
        ws.ours = false;
        return;
    }
    if (RectCoversMonitor(h) && !RectIsWorkArea(h)) ws.ours = false;
}

// 目前是不是本工具可以控制的狀態：視窗模式，或本工具套用的無邊框
static bool IsControllable(HWND h, WinState& ws) {
    UpdateOursFlag(h, ws);
    return HasCaption(h) || ws.ours;
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
    GetState(h).ours = true;   // 這個無邊框是本工具套用的
}

static void RestoreWindow(HWND h, WinState& ws) {
    ws.ours = false;
    if (IsIconic(h) || IsZoomed(h)) ShowWindow(h, SW_RESTORE);
    LONG_PTR s = GetWindowLongPtrW(h, GWL_STYLE) | (LONG_PTR)(WS_CAPTION | WS_THICKFRAME | WS_MAXIMIZEBOX);
    if (g_locked && g_lockStyle == 1) s &= ~(LONG_PTR)(WS_THICKFRAME | WS_MAXIMIZEBOX);
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
    bool handled = false;
    for (size_t i = 0; i < wins.size(); ++i) {
        HWND h = wins[i];
        WinState& ws = GetState(h);
        UpdateOursFlag(h, ws);
        if (HasCaption(h)) {   // 視窗模式：切換成無邊框
            ws.managed = true;
            if (IsIconic(h) || IsZoomed(h)) ShowWindow(h, SW_RESTORE);
            SaveClient(h, ws);
            ApplyBorderless(h);
            g_borderless = true;
            handled = true;
        } else if (ws.ours) {   // 本工具套用的無邊框：還原回視窗模式
            ws.managed = true;
            RestoreWindow(h, ws);
            g_borderless = false;
            handled = true;
        }
        // 其他：遊戲自己的全螢幕 / 無邊框全視窗模式，不處理
    }
    if (!handled) {
        Notify(T(S_TIP_WINDOWED));
        return;
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
    bool handled = false;
    for (size_t i = 0; i < wins.size(); ++i) {
        WinState& ws = GetState(wins[i]);
        if (!IsControllable(wins[i], ws)) continue;   // 遊戲自己的全螢幕 / 無邊框全視窗模式：不處理
        ws.managed = true;
        RestoreWindow(wins[i], ws);
        handled = true;
    }
    if (!handled) {
        Notify(T(S_TIP_WINDOWED));
        return;
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
    bool sawCaption = false, sawOurs = false;
    for (size_t i = 0; i < wins.size(); ++i) {
        HWND h = wins[i];
        WinState& ws = GetState(h);
        ws.managed = true;
        if (HasCaption(h)) {
            sawCaption = true;
            SaveClient(h, ws);
            if (g_lockStyle == 1) {   // 舊做法的鎖定會移除縮放邊框：依視窗樣式判斷目前是否鎖定
                LONG_PTR st = GetWindowLongPtrW(h, GWL_STYLE);
                g_locked = ((st & WS_THICKFRAME) == 0);
            }
            if (g_locked) EnsureLockState(h);
        } else if (RectIsWorkArea(h)) {
            ws.ours = true;   // 鋪滿工作區的無邊框：視為之前由本工具套用的 (本工具重新啟動)
            sawOurs = true;
        }
        // 其他：遊戲自己的全螢幕 / 無邊框全視窗模式，不當作本工具的無邊框
    }
    if (sawOurs) g_borderless = true;
    else if (sawCaption) g_borderless = false;   // 只有遊戲自己的全螢幕時，沿用設定檔記錄的狀態
}

// 每 500ms：偵測「新出現的遊戲視窗」(重啟遊戲後)，穩定後自動套用目前的無邊框/鎖定狀態
// ---------------------------------------------------------------------------
//  隱藏遊戲在工作列上的按鈕 (ITaskbarList::DeleteTab / AddTab)
//  只影響工作列按鈕，不改變視窗本身
// ---------------------------------------------------------------------------
static bool EnsureTaskbarList() {
    if (g_taskbarList) return true;
    ITaskbarList* tl = NULL;
    if (FAILED(CoCreateInstance(__uuidof(TaskbarList), NULL, CLSCTX_INPROC_SERVER, IID_PPV_ARGS(&tl))) || !tl) return false;
    if (FAILED(tl->HrInit())) {
        tl->Release();
        return false;
    }
    g_taskbarList = tl;
    return true;
}

static void ReleaseTaskbarList() {
    if (g_taskbarList) {
        g_taskbarList->Release();
        g_taskbarList = NULL;
    }
}

// 對所有遊戲視窗套用 (hide = true：隱藏工作列按鈕；false：顯示)
static void ApplyTaskbarButtons(bool hide) {
    if (!EnsureTaskbarList()) return;
    for (std::map<HWND, WinState>::iterator it = g_wins.begin(); it != g_wins.end(); ++it) {
        if (!IsWindow(it->first)) continue;
        if (hide) g_taskbarList->DeleteTab(it->first);
        else g_taskbarList->AddTab(it->first);
    }
    g_tbLastApply = GetTickCount64();
}

// ---------------------------------------------------------------------------
//  限制滑鼠移動範圍 (ClipCursor)
//  避免遊戲在全螢幕模式下，滑鼠移到畫面邊緣時觸發視角變化：
//  只有在「選單已啟用、遊戲為前景視窗、而且處於全螢幕模式」時，才把滑鼠限制在遊戲畫面內縮 g_mouseClipMargin 像素的範圍內；
//  其餘情況 (切到別的視窗、最小化、離開全螢幕、關閉功能、結束本工具) 一律立刻放掉
// ---------------------------------------------------------------------------
// 全螢幕模式：視窗沒有標題列，而且完全涵蓋所在的整個螢幕
static bool IsFullscreenWindow(HWND h) {
    return !HasCaption(h) && RectCoversMonitor(h);
}

// 系統目前是否有 Direct3D 獨佔全螢幕的程式在執行 (遊戲的「全螢幕模式」；「無邊框全視窗模式」不算)。
// 回傳 SHQueryUserNotificationState 的狀態值，查詢失敗時回傳 -1
static int QueryD3DFullscreenState() {
    QUERY_USER_NOTIFICATION_STATE st;
    if (FAILED(SHQueryUserNotificationState(&st))) return -1;
    return (int)st;
}

// 前景視窗是不是遊戲的視窗：已追蹤的遊戲主視窗，或和遊戲同一個行程的其他視窗
// (從 Alt+Tab 回到遊戲時，前景視窗不一定剛好是已追蹤的主視窗)
static bool IsGameForeground(HWND fg) {
    if (!fg) return false;
    if (g_wins.find(fg) != g_wins.end()) return true;
    DWORD pid = 0;
    GetWindowThreadProcessId(fg, &pid);
    return pid != 0 && pid == g_gamePid;
}

// 放掉本工具設定的滑鼠限制 (不處理計時器)
static void ReleaseClipOnly() {
    if (!g_clipActive) return;
    RECT cur;
    if (GetClipCursor(&cur) && EqualRect(&cur, &g_clipRect)) ClipCursor(NULL);   // 只放掉自己設定的，不動遊戲等其他程式設定的
    g_clipActive = false;
}

// 完全停止 (結束本工具時)
static void ReleaseMouseClip() {
    ReleaseClipOnly();
    if (g_clipTimerOn) {
        KillTimer(g_hWnd, 7);
        g_clipTimerOn = false;
    }
}

static void UpdateMouseClip() {
    if (!g_mouseClip && !g_clipActive) return;
    HWND fg = GetForegroundWindow();
    bool gameFg = g_mouseClip && IsGameForeground(fg);
    bool want = false;
    RECT r = { 0, 0, 0, 0 }, wr = { 0, 0, 0, 0 }, mr = { 0, 0, 0, 0 };
    bool iconic = false, caption = false, full = false, exclusive = false, topmost = false;
    unsigned long wstyle = 0, wexstyle = 0;
    int quns = -1;
    if (gameFg) {
        iconic = IsIconic(fg) != 0;
        caption = HasCaption(fg);
        full = IsFullscreenWindow(fg);
        wstyle = (unsigned long)GetWindowLongPtrW(fg, GWL_STYLE);
        wexstyle = (unsigned long)GetWindowLongPtrW(fg, GWL_EXSTYLE);
        topmost = (wexstyle & WS_EX_TOPMOST) != 0;
        if (full) {
            quns = QueryD3DFullscreenState();
            exclusive = (quns == QUNS_RUNNING_D3D_FULL_SCREEN);
        }
        GetWindowRect(fg, &wr);
        MONITORINFO mi;
        ZeroMemory(&mi, sizeof(mi));
        mi.cbSize = sizeof(mi);
        if (GetMonitorInfoW(MonitorFromWindow(fg, MONITOR_DEFAULTTONEAREST), &mi)) mr = mi.rcMonitor;
        if (!iconic && full && (exclusive || g_mouseClipBorderless)) {   // 只在全螢幕模式 (獨佔全螢幕) 限制；ini 的 MouseClipBorderless=1 時無邊框全視窗模式也限制
            RECT cr;
            if (GetClientRect(fg, &cr)) {
                POINT tl = { cr.left, cr.top }, br = { cr.right, cr.bottom };
                ClientToScreen(fg, &tl);
                ClientToScreen(fg, &br);
                int w = br.x - tl.x, h = br.y - tl.y;
                int m = std::min(g_mouseClipMargin, std::max(0, (std::min(w, h) - 2) / 2));   // 避免範圍縮到沒有大小
                r.left = tl.x + m;
                r.top = tl.y + m;
                r.right = br.x - m;
                r.bottom = br.y - m;
                want = (r.right - r.left > 0 && r.bottom - r.top > 0);
            }
        }
    }
    if (gameFg) {   // 診斷：只記錄遊戲為前景時的狀態，內容有變化才更新
        RECT sys = { 0, 0, 0, 0 };
        GetClipCursor(&sys);
        char b[480];
        snprintf(b, sizeof(b), "mouseclip: game foreground, iconic=%d caption=%d fullscreen=%d d3dState=%d exclusive=%d topmost=%d style=0x%08lX exStyle=0x%08lX locked=%d lockStyle=%d window=[%ld,%ld,%ld,%ld] monitor=[%ld,%ld,%ld,%ld] want=%d active=%d target=[%ld,%ld,%ld,%ld] systemClip=[%ld,%ld,%ld,%ld]",
                 iconic ? 1 : 0, caption ? 1 : 0, full ? 1 : 0, quns, exclusive ? 1 : 0, topmost ? 1 : 0, wstyle, wexstyle, g_locked ? 1 : 0, g_lockStyle,
                 (long)wr.left, (long)wr.top, (long)wr.right, (long)wr.bottom, (long)mr.left, (long)mr.top, (long)mr.right, (long)mr.bottom,
                 want ? 1 : 0, g_clipActive ? 1 : 0, (long)r.left, (long)r.top, (long)r.right, (long)r.bottom,
                 (long)sys.left, (long)sys.top, (long)sys.right, (long)sys.bottom);
        std::string cur = b;
        if (cur != g_clipDbg) {
            g_clipDbg = cur;
            g_clipDbgTick = GetTickCount64();
        }
    }
    // 計時器：只有「功能啟用而且遊戲是前景」時才每 0.2 秒確認一次，
    // 所以全螢幕切換、從 Alt+Tab 回來這類過渡狀態都會在 0.2 秒內補上；不在遊戲裡時沒有計時器
    if (gameFg && !g_clipTimerOn) {
        SetTimer(g_hWnd, 7, 200, NULL);
        g_clipTimerOn = true;
    } else if (!gameFg && g_clipTimerOn) {
        KillTimer(g_hWnd, 7);
        g_clipTimerOn = false;
    }
    if (!want) {
        ReleaseClipOnly();
        return;
    }
    RECT cur;
    if (!g_clipActive || !GetClipCursor(&cur) || !EqualRect(&cur, &r)) {   // 遊戲自己改了限制範圍時再設定回來
        ClipCursor(&r);
        g_clipRect = r;
        g_clipActive = true;
    }
}

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
            if (g_lockStyle == 1 && !g_borderless && !IsIconic(h) && (GetWindowLongPtrW(h, GWL_STYLE) & WS_THICKFRAME)) {
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
    // 隱藏遊戲工作列按鈕：遊戲視窗改變 (例如遊戲重啟) 時立刻套用，之後每 5 秒再確認一次
    // (視窗最小化 / 還原、explorer 重啟等情況下，按鈕可能被系統重新加回來)
    if (g_hideTaskbar && !g_wins.empty()) {
        size_t sig = 1;
        for (std::map<HWND, WinState>::iterator it = g_wins.begin(); it != g_wins.end(); ++it) sig = sig * 31 + (size_t)it->first;
        if (sig != g_tbSig || GetTickCount64() - g_tbLastApply >= 5000) {
            g_tbSig = sig;
            ApplyTaskbarButtons(true);
        }
    }
    UpdateMouseClip();   // 限制滑鼠移動範圍 (依目前的前景視窗確認)
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

struct StaleIconCtx { std::vector<DWORD> pids; };

static BOOL CALLBACK RecoverIconEnum(HWND w, LPARAM lp);

static HICON QueryWndIcon(HWND w, WPARAM type) {
    DWORD_PTR res = 0;
    if (!SendMessageTimeoutW(w, WM_GETICON, type, 0, SMTO_ABORTIFHUNG | SMTO_BLOCK, 300, &res)) return NULL;
    return (HICON)res;
}

// 本工具被強制結束時 (例如 build.bat 重新建置)，記憶體裡的原本圖示會遺失，遊戲視窗會一直留著藍色圖示。
// 所以換成藍色圖示之前，先把「原本的圖示」記在遊戲視窗的視窗屬性上；本工具下次啟動時 (RecoverStaleIcons) 用它換回去
static const wchar_t* const kPropIconBlue = L"ClientManager.IconBlue";
static const wchar_t* const kPropIconBig = L"ClientManager.OrigBig";
static const wchar_t* const kPropIconSmall = L"ClientManager.OrigSmall";

static void ClearIconProps(HWND w) {
    RemovePropW(w, kPropIconBlue);
    RemovePropW(w, kPropIconBig);
    RemovePropW(w, kPropIconSmall);
}

static bool SetWndIcon(HWND w, WPARAM type, HICON ic) {
    DWORD_PTR res = 0;
    return SendMessageTimeoutW(w, WM_SETICON, type, (LPARAM)ic, SMTO_ABORTIFHUNG | SMTO_BLOCK, 300, &res) != 0;
}

static BOOL CALLBACK RecoverIconEnum(HWND w, LPARAM lp) {
    StaleIconCtx* c = (StaleIconCtx*)lp;
    if (!GetPropW(w, kPropIconBlue)) return TRUE;
    DWORD pid = 0;
    GetWindowThreadProcessId(w, &pid);
    if (std::find(c->pids.begin(), c->pids.end(), pid) == c->pids.end()) return TRUE;
    SetWndIcon(w, ICON_BIG, (HICON)GetPropW(w, kPropIconBig));
    SetWndIcon(w, ICON_SMALL, (HICON)GetPropW(w, kPropIconSmall));
    ClearIconProps(w);
    return TRUE;
}

// 上次若被強制結束，遊戲視窗可能還留著藍色圖示：用視窗屬性裡記錄的原本圖示換回去
static void RecoverStaleIcons() {
    StaleIconCtx c;
    c.pids = GetClientPids();
    if (c.pids.empty()) return;
    EnumWindows(RecoverIconEnum, (LPARAM)&c);
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
    if (ok1 && ok2) ClearIconProps(w);
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
    SetPropW(t.wnd, kPropIconBig, (HANDLE)t.restBig);       // 先記下原本的圖示，再換成藍色
    SetPropW(t.wnd, kPropIconSmall, (HANDLE)t.restSmall);
    SetPropW(t.wnd, kPropIconBlue, (HANDLE)1);
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
        // 只在使用者按著滑鼠左鍵拖曳時才取消 (遊戲自己改視窗時不去送按鍵給遊戲)；
        // 先把目前位置當成鎖定位置，這樣遊戲自己移動過視窗之後，取消拖曳時不會被拉回舊位置
        if (GetAsyncKeyState(VK_LBUTTON) & 0x8000) {
            UpdateLockPos(h);
            PostMessageW(h, WM_KEYDOWN, VK_ESCAPE, 0x00010001);   // 等同在移動 / 縮放中按 Esc：取消
        }
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
        WinState& ws = it->second;
        if (!ws.managed || !IsWindow(h) || IsIconic(h)) continue;
        if (!HasCaption(h)) {
            // 沒有標題列：只處理「本工具套用的無邊框」；遊戲自己的全螢幕 / 無邊框全視窗模式不去干涉
            UpdateOursFlag(h, ws);
            if (g_borderless && ws.ours && !RectIsWorkArea(h)) {   // 遊戲改了我們的無邊框視窗的大小 (例如環境設定按取消)：重新鋪滿
                LimitPause lp;
                ApplyBorderless(h);
                ++g_fixCount;
            }
            continue;
        }
        if (g_borderless) {   // 遊戲回到視窗模式：先記下視窗模式的大小與位置，再依目前的無邊框模式套用
            LimitPause lp;
            SaveClient(h, ws);
            ApplyBorderless(h);
            ++g_fixCount;
        } else if (g_locked && g_lockStyle == 1 && (GetWindowLongPtrW(h, GWL_STYLE) & WS_THICKFRAME)) {
            LimitPause lp;
            ApplyLock(h, true);
            ++g_fixCount;
        }
    }
}


static void CALLBACK WinEventProc(HWINEVENTHOOK, DWORD ev, HWND hwnd, LONG idObject, LONG, DWORD, DWORD) {
    if (ev == EVENT_SYSTEM_FOREGROUND || ev == EVENT_SYSTEM_MINIMIZESTART || ev == EVENT_SYSTEM_MINIMIZEEND) {
        g_tbLastApply = 0;   // 下一次偵測時重新隱藏工作列按鈕
        UpdateMouseClip();   // 前景改變時立刻套用 / 放掉滑鼠範圍限制
    }
    if (ev == EVENT_OBJECT_LOCATIONCHANGE) {   // 只會收到遊戲行程的事件 (UpdateGameHook 以遊戲 PID 篩選)
        if (idObject == OBJID_WINDOW && hwnd && (hwnd == g_gameHwnd || g_wins.find(hwnd) != g_wins.end())) {
            UpdateMouseClip();   // 遊戲切換全螢幕 / 視窗模式或解析度時重新判斷
            ScheduleModeCheck();
        }
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
    if (!g_clipDbg.empty()) {   // 滑鼠範圍限制：遊戲最後一次為前景時的判斷細節 (這個函式只在 UI 執行緒呼叫)
        char b[96];
        snprintf(b, sizeof(b), "  (state when the game was last in the foreground, %llu s ago)\r\n", (unsigned long long)((GetTickCount64() - g_clipDbgTick) / 1000));
        out += g_clipDbg + b;
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
    if (g_monPreview && (!g_ovEnabled || !s.game)) s = DemoSample();
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
//   * 設定視窗顯示「效能監控」頁期間固定顯示 (預覽)，不受「只在遊戲前景時顯示」影響
//   * 平常：啟用監控且遊戲執行中才顯示；遊戲最小化時隱藏
//   * 「只在遊戲前景時顯示」：前景不是遊戲就隱藏；但前景是本工具 (選單) 或工作列 / 縮圖預覽時維持原狀，避免閃爍
//   * 顯示期間每 40 毫秒檢查一次有沒有被工作列等視窗蓋住，被蓋住才立刻重新置頂
static void UpdateOverlayVisibility() {
    ImgUpdateVisibility();   // 圖片置頂也依前景視窗 / 遊戲狀態更新 (同樣的時機)
    if (!g_ovHwnd) return;
    bool want = false;
    DWORD gp = g_gamePid;
    if (g_monPreview) {
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

// ===========================================================================
//  圖片置頂 (料理尺)：最多 10 組，每組一個獨立的分層視窗 (WS_EX_LAYERED，每個像素獨立 Alpha)
//  * 圖片以 GDI+ 解碼：靜態圖片轉成 32bpp 預乘 Alpha 位圖後就釋放檔案串流；GIF 保留串流，每個影格播放時才解碼
//  * 選擇檔案後不複製，只記錄原始路徑；檔案遺失時顯示占位框
//  * 未鎖定：半透明深色背景 + 四角縮放控制點，可拖曳 / 縮放 / 方向鍵微調；鎖定：沒有背景與控制點，整個視窗滑鼠穿透
//  * 只有「啟用 + 總開關開啟」的組別才會建立視窗並載入圖片；其餘不佔用記憶體與 CPU
//  * 只在 UI 執行緒使用
// ===========================================================================
static const int kImgGroups = 10;
static const int kImgPad = 10;                         // 未鎖定時，圖片四周留給縮放控制點的邊 (像素)
static const int kImgMinShort = 4;                     // 縮放後短邊的最小像素數
static const int kImgMinLong = 24;                     // 縮放後長邊的最小像素數
static const int kImgMaxSide = 7680;                   // 縮放後單邊的最大像素數
static const long long kImgMaxPixels = 16LL * 1024 * 1024;   // 縮放後的最大像素數 (限制記憶體用量)
static const int kImgPlaceholderW = 260, kImgPlaceholderH = 44;   // 圖片遺失 / 未選擇時的占位框大小
static const int kRulerW = 300, kRulerH = 9;           // 內建料理尺：目前遊戲版本的實際像素大小
static const char* const kRulerHex[9] = {
    "8000000200000008000000200000008000000200000008000000200000008000000200000010",
    "8000000200000008000000200000008000000200000008000000200000008000000200000010",
    "8000000200000008000000200000008000000200000008000000200000008000000200000010",
    "8000000200000008000000200000008000000200000008000000200000008000000200000010",
    "80010012000400E8001003A00040028001003A000400E8001003A000400E8001003A000404F0",
    "8001003200040028001000A00040068001002200040088001002A000400A8001002A00040CB0",
    "80010012000400E8001003A000400A8001003A000400E8001000A000400E8001003A000404B0",
    "8001001200040088001000A000400E8001000A000400A8001000A000400A8001000A000404B0",
    "8001003A000400E8001003A00040028001003A000400E8001000A000400E8001003A00040EF0"
};

struct ImgGroup {
    // ---- 設定 (存入 ClientManager.ini 的 [ImageN]) ----
    bool enabled, locked, fgOnly, flipH, gifPaused;
    int source;        // 0 = 內建料理尺 (白)，1 = 內建料理尺 (黑)，2 = 內建料理尺 (自訂顏色)，3 = 自選圖片
    unsigned int rulerColor;   // source = 2 時的顏色 (0xRRGGBB)
    int opacity;       // 5 ~ 100 (%)
    int scale;         // 縮放比例 (%)，相對於旋轉後的原始大小
    int rot;           // 0 / 90 / 180 / 270 (順時針)
    int gifSpeed;      // GIF 播放速度 (%)
    int z;             // 層級：0 = 最底層 ... 9 = 最上層 (10 組各佔一個，不重複)
    int x, y;          // 圖片左上角，相對於所在螢幕左上角 (像素)
    std::wstring name, path, monitor;
    // ---- 執行階段 ----
    HWND hwnd;
    Gdiplus::Bitmap* bmp;
    IStream* stream;
    int srcW, srcH, frames, frame;
    std::vector<int> delays;   // 每個影格的顯示時間 (毫秒)
    bool missing, loaded, shown;
    std::wstring loadedSig;
    HDC dc;
    HBITMAP dib;
    HGDIOBJ oldBmp;
    void* bits;
    int dibW, dibH;
    ImgGroup() : enabled(false), locked(false), fgOnly(false), flipH(false), gifPaused(false),
                 source(0), rulerColor(0xFFFFFFu), opacity(100), scale(100), rot(0), gifSpeed(100), z(0), x(100), y(100),
                 hwnd(NULL), bmp(NULL), stream(NULL), srcW(0), srcH(0), frames(1), frame(0),
                 missing(false), loaded(false), shown(false), dc(NULL), dib(NULL), oldBmp(NULL), bits(NULL), dibW(0), dibH(0) {}
};

static ImgGroup g_img[kImgGroups];
static ULONG_PTR g_gdipToken = 0;
static bool g_gdipOn = false;
static bool g_imgClassReg = false;

static void ImgNotifyDlg(int idx);   // 通知設定視窗：圖片被拖曳 / 縮放 / 微調後更新欄位 (idx = -1 代表全部重新載入)

static std::wstring ImgSec(int i) {
    wchar_t b[16];
    wsprintfW(b, L"Image%d", i + 1);
    return b;
}

static void SaveStringS(const std::wstring& sec, const wchar_t* key, const std::wstring& v) {
    EnsureUnicodeIni();
    WritePrivateProfileStringW(sec.c_str(), key, v.c_str(), g_iniPath.c_str());
}

static void SaveIntS(const std::wstring& sec, const wchar_t* key, int v) {
    wchar_t b[16];
    wsprintfW(b, L"%d", v);
    SaveStringS(sec, key, b);
}

static bool IniHasS(const std::wstring& sec, const wchar_t* key) {
    wchar_t b[8];
    b[0] = 0;
    GetPrivateProfileStringW(sec.c_str(), key, L"", b, 8, g_iniPath.c_str());
    return b[0] != 0;
}

static int IniIntS(const std::wstring& sec, const wchar_t* key, int def, int lo, int hi) {
    wchar_t b[32];
    b[0] = 0;
    GetPrivateProfileStringW(sec.c_str(), key, L"", b, 32, g_iniPath.c_str());
    if (!b[0]) return def;
    int v = _wtoi(b);
    return std::max(lo, std::min(hi, v));
}

static std::wstring IniStrS(const std::wstring& sec, const wchar_t* key, DWORD maxLen) {
    std::vector<wchar_t> b(maxLen + 1);
    b[0] = 0;
    GetPrivateProfileStringW(sec.c_str(), key, L"", b.data(), maxLen, g_iniPath.c_str());
    return b.data();
}

// 層級由低到高的組別編號
static void ImgZOrder(int* order) {
    for (int k = 0; k < kImgGroups; ++k) order[k] = k;
    std::sort(order, order + kImgGroups, [](int a, int b) {
        if (g_img[a].z != g_img[b].z) return g_img[a].z < g_img[b].z;
        return a < b;
    });
}

// 6 位數 16 進位顏色 (RRGGBB，可以有前面的 #)；格式不對時回傳 def
static unsigned int ParseHexColor(const std::wstring& in, unsigned int def, bool* ok = NULL) {
    std::wstring t = in;
    while (!t.empty() && (t.front() == L' ' || t.front() == L'#')) t.erase(t.begin());
    while (!t.empty() && t.back() == L' ') t.pop_back();
    bool good = (t.size() == 6);
    unsigned int v = 0;
    for (size_t k = 0; good && k < 6; ++k) {
        wchar_t ch = t[k];
        int d = (ch >= L'0' && ch <= L'9') ? ch - L'0' : (ch >= L'A' && ch <= L'F') ? ch - L'A' + 10 : (ch >= L'a' && ch <= L'f') ? ch - L'a' + 10 : -1;
        if (d < 0) good = false;
        else v = v * 16 + (unsigned int)d;
    }
    if (ok) *ok = good;
    return good ? v : def;
}

static std::wstring HexColorText(unsigned int rgb) {
    wchar_t b[16];
    wsprintfW(b, L"%06X", rgb & 0xFFFFFFu);
    return b;
}

static void ImgSetDefaults(int i) {
    ImgGroup& g = g_img[i];
    g.enabled = false;
    g.locked = false;
    g.fgOnly = false;
    g.flipH = false;
    g.gifPaused = false;
    g.source = (i == 1) ? 1 : 0;   // 第 2 組預設用黑色料理尺
    g.rulerColor = 0xFFFFFFu;
    g.opacity = 100;
    g.scale = 100;
    g.rot = 0;
    g.gifSpeed = 100;
    g.z = i;
    g.x = 100;
    g.y = 100 + i * 30;
    g.name.clear();
    g.path.clear();
    g.monitor.clear();
}

static void ImgLoadSettings() {
    g_imgMaster = IniBool(L"ImgMaster", 0);
    g_imgLockAll = IniBool(L"ImgLockAll", 0);
    for (int i = 0; i < kImgGroups; ++i) {
        ImgSetDefaults(i);
        ImgGroup& g = g_img[i];
        std::wstring s = ImgSec(i);
        g.enabled = IniIntS(s, L"Enabled", 0, 0, 1) != 0;
        g.locked = IniIntS(s, L"Locked", 0, 0, 1) != 0;
        g.fgOnly = IniIntS(s, L"FgOnly", 0, 0, 1) != 0;
        g.name = IniStrS(s, L"Name", 40);
        g.source = IniIntS(s, L"Source", g.source, 0, 3);
        g.rulerColor = ParseHexColor(IniStrS(s, L"RulerColor", 16), 0xFFFFFFu);
        g.path = IniStrS(s, L"Path", 1000);
        g.opacity = IniIntS(s, L"Opacity", 100, 5, 100);
        g.scale = IniIntS(s, L"Scale", 100, 1, 10000);   // 實際的範圍在載入圖片後，依圖片大小修正
        g.monitor = IniStrS(s, L"Monitor", 60);
        g.x = IniIntS(s, L"X", g.x, -100000, 100000);
        g.y = IniIntS(s, L"Y", g.y, -100000, 100000);
        g.flipH = IniIntS(s, L"FlipH", 0, 0, 1) != 0;
        g.rot = ((IniIntS(s, L"Rotate", 0, 0, 359) + 45) / 90 % 4) * 90;
        g.gifPaused = IniIntS(s, L"GifPaused", 0, 0, 1) != 0;
        g.gifSpeed = IniIntS(s, L"GifSpeed", 100, 10, 1000);
        g.z = IniIntS(s, L"Z", i, 0, kImgGroups - 1);
    }
    int order[kImgGroups];   // 層級必須是 0 ~ 9 的排列：重複或缺少時依目前順序重新編號
    ImgZOrder(order);
    for (int k = 0; k < kImgGroups; ++k) g_img[order[k]].z = k;
}

static void ImgSaveAll(int i) {
    const ImgGroup& g = g_img[i];
    std::wstring s = ImgSec(i);
    SaveIntS(s, L"Enabled", g.enabled ? 1 : 0);
    SaveIntS(s, L"Locked", g.locked ? 1 : 0);
    SaveIntS(s, L"FgOnly", g.fgOnly ? 1 : 0);
    SaveStringS(s, L"Name", g.name);
    SaveIntS(s, L"Source", g.source);
    SaveStringS(s, L"RulerColor", HexColorText(g.rulerColor));
    SaveStringS(s, L"Path", g.path);
    SaveIntS(s, L"Opacity", g.opacity);
    SaveIntS(s, L"Scale", g.scale);
    SaveStringS(s, L"Monitor", g.monitor);
    SaveIntS(s, L"X", g.x);
    SaveIntS(s, L"Y", g.y);
    SaveIntS(s, L"FlipH", g.flipH ? 1 : 0);
    SaveIntS(s, L"Rotate", g.rot);
    SaveIntS(s, L"GifPaused", g.gifPaused ? 1 : 0);
    SaveIntS(s, L"GifSpeed", g.gifSpeed);
    SaveIntS(s, L"Z", g.z);
}

// 拖曳 / 縮放 / 方向鍵後只更新位置與大小
static void ImgSaveGeom(int i) {
    const ImgGroup& g = g_img[i];
    std::wstring s = ImgSec(i);
    SaveStringS(s, L"Monitor", g.monitor);
    SaveIntS(s, L"X", g.x);
    SaveIntS(s, L"Y", g.y);
    SaveIntS(s, L"Scale", g.scale);
}

// 設定檔裡還沒有的組別，補上完整的預設值 (已經有的不動，保留使用者加的註解)
static void ImgSaveMissing() {
    for (int i = 0; i < kImgGroups; ++i) {
        if (!IniHasS(ImgSec(i), L"Enabled")) ImgSaveAll(i);
    }
}

static bool ImgIsLocked(int i) { return g_imgLockAll || g_img[i].locked; }

static bool ImgEnsureGdip() {
    if (g_gdipOn) return true;
    Gdiplus::GdiplusStartupInput in;
    if (Gdiplus::GdiplusStartup(&g_gdipToken, &in, NULL) != Gdiplus::Ok) return false;
    g_gdipOn = true;
    return true;
}

// 內建料理尺：從遊戲截圖取出的刻度 (300 x 9 像素)，白色 / 黑色 / 自訂顏色，背景透明
static Gdiplus::Bitmap* ImgMakeRuler(unsigned int rgb) {
    Gdiplus::Bitmap* b = new Gdiplus::Bitmap(kRulerW, kRulerH, PixelFormat32bppPARGB);
    if (b->GetLastStatus() != Gdiplus::Ok) {
        delete b;
        return NULL;
    }
    Gdiplus::BitmapData bd;
    Gdiplus::Rect r(0, 0, kRulerW, kRulerH);
    if (b->LockBits(&r, Gdiplus::ImageLockModeWrite, PixelFormat32bppPARGB, &bd) != Gdiplus::Ok) {
        delete b;
        return NULL;
    }
    const unsigned int col = 0xFF000000u | (rgb & 0xFFFFFFu);   // 不透明，預乘 Alpha 後的顏色不變
    for (int y = 0; y < kRulerH; ++y) {
        unsigned int* row = (unsigned int*)((BYTE*)bd.Scan0 + (ptrdiff_t)y * bd.Stride);
        const char* hex = kRulerHex[y];
        for (int x = 0; x < kRulerW; ++x) {
            int bi = x >> 3;
            int hi = hex[bi * 2], lo = hex[bi * 2 + 1];
            int v = (hi <= '9' ? hi - '0' : hi - 'A' + 10) * 16 + (lo <= '9' ? lo - '0' : lo - 'A' + 10);
            row[x] = ((v >> (7 - (x & 7))) & 1) ? col : 0u;
        }
    }
    b->UnlockBits(&bd);
    return b;
}

static std::wstring ImgSigOf(const ImgGroup& g) {
    if (g.source == 3) return L"F|" + g.path;
    if (g.source == 2) return L"B2|" + HexColorText(g.rulerColor);
    return g.source == 1 ? L"B1" : L"B0";
}

static void ImgFreeImage(int i) {
    ImgGroup& g = g_img[i];
    if (g.bmp) {
        delete g.bmp;
        g.bmp = NULL;
    }
    if (g.stream) {
        g.stream->Release();
        g.stream = NULL;
    }
    g.srcW = g.srcH = 0;
    g.frames = 1;
    g.frame = 0;
    g.delays.clear();
    g.missing = false;
    g.loaded = false;
    g.loadedSig.clear();
}

static void ImgFreeDib(int i) {
    ImgGroup& g = g_img[i];
    if (g.dc && g.oldBmp) SelectObject(g.dc, g.oldBmp);
    if (g.dib) DeleteObject(g.dib);
    if (g.dc) DeleteDC(g.dc);
    g.dib = NULL;
    g.dc = NULL;
    g.oldBmp = NULL;
    g.bits = NULL;
    g.dibW = g.dibH = 0;
}

// 讀取圖片檔：整個檔案讀進記憶體後解碼，不會鎖住原始檔案 (檔案可以隨時移動 / 刪除)
static bool ImgLoadFile(int i, const std::wstring& path) {
    ImgGroup& g = g_img[i];
    HANDLE h = CreateFileW(path.c_str(), GENERIC_READ, FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE, NULL, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL);
    if (h == INVALID_HANDLE_VALUE) return false;
    LARGE_INTEGER sz;
    if (!GetFileSizeEx(h, &sz) || sz.QuadPart <= 0 || sz.QuadPart > 256LL * 1024 * 1024) {
        CloseHandle(h);
        return false;
    }
    HGLOBAL hg = GlobalAlloc(GMEM_MOVEABLE, (SIZE_T)sz.QuadPart);
    if (!hg) {
        CloseHandle(h);
        return false;
    }
    void* p = GlobalLock(hg);
    DWORD rd = 0;
    BOOL ok = p ? ReadFile(h, p, (DWORD)sz.QuadPart, &rd, NULL) : FALSE;
    if (p) GlobalUnlock(hg);
    CloseHandle(h);
    if (!ok || rd != (DWORD)sz.QuadPart) {
        GlobalFree(hg);
        return false;
    }
    IStream* st = NULL;
    if (CreateStreamOnHGlobal(hg, TRUE, &st) != S_OK || !st) {   // TRUE：串流釋放時一併釋放記憶體
        GlobalFree(hg);
        return false;
    }
    Gdiplus::Bitmap* b = Gdiplus::Bitmap::FromStream(st, FALSE);
    if (!b || b->GetLastStatus() != Gdiplus::Ok) {
        delete b;
        st->Release();
        return false;
    }
    UINT w = b->GetWidth(), hgt = b->GetHeight();
    if (w == 0 || hgt == 0 || (unsigned long long)w * hgt > 50000000ULL) {   // 超過 5000 萬像素的圖片不載入 (記憶體用量)
        delete b;
        st->Release();
        return false;
    }
    UINT frames = 1;
    bool anim = false;
    UINT dimCount = b->GetFrameDimensionsCount();
    if (dimCount > 0) {
        std::vector<GUID> ids(dimCount);
        b->GetFrameDimensionsList(ids.data(), dimCount);
        if (IsEqualGUID(ids[0], Gdiplus::FrameDimensionTime)) {
            UINT n = b->GetFrameCount(&ids[0]);
            if (n > 1) {
                frames = n;
                anim = true;
            }
        }
    }
    std::vector<int> delays;
    if (anim) {
        UINT psz = b->GetPropertyItemSize(PropertyTagFrameDelay);
        if (psz > 0) {
            std::vector<BYTE> buf(psz);
            Gdiplus::PropertyItem* pi = (Gdiplus::PropertyItem*)buf.data();
            if (b->GetPropertyItem(PropertyTagFrameDelay, psz, pi) == Gdiplus::Ok) {
                const UINT* d = (const UINT*)pi->value;
                UINT cnt = pi->length / (UINT)sizeof(UINT);
                for (UINT k = 0; k < frames; ++k) delays.push_back((int)((k < cnt) ? d[k] : 10) * 10);   // 單位：1/100 秒
            }
        }
        if (delays.empty()) delays.assign(frames, 100);
    }
    Gdiplus::Bitmap* useBmp = b;
    IStream* useStream = st;
    if (!anim) {   // 靜態圖片：轉成 32bpp 預乘 Alpha 位圖，之後不再需要原始檔案的資料
        Gdiplus::Bitmap* pb = new Gdiplus::Bitmap((INT)w, (INT)hgt, PixelFormat32bppPARGB);
        bool good = (pb->GetLastStatus() == Gdiplus::Ok);
        if (good) {
            Gdiplus::Graphics gg(pb);
            gg.SetCompositingMode(Gdiplus::CompositingModeSourceCopy);
            good = (gg.DrawImage(b, Gdiplus::Rect(0, 0, (INT)w, (INT)hgt), 0, 0, (INT)w, (INT)hgt, Gdiplus::UnitPixel) == Gdiplus::Ok);
        }
        delete b;
        st->Release();
        if (!good) {
            delete pb;
            return false;
        }
        useBmp = pb;
        useStream = NULL;
    }
    g.bmp = useBmp;
    g.stream = useStream;
    g.srcW = (int)w;
    g.srcH = (int)hgt;
    g.frames = (int)frames;
    g.frame = 0;
    g.delays = delays;
    return true;
}

// 載入這一組的圖片。成功回傳 true；失敗 (檔案遺失 / 無法解碼 / 尚未選擇) 時 missing = true，顯示占位框
static bool ImgLoad(int i) {
    ImgGroup& g = g_img[i];
    ImgFreeImage(i);
    g.loaded = true;
    g.loadedSig = ImgSigOf(g);
    if (g.source != 3) {
        Gdiplus::Bitmap* b = ImgMakeRuler(g.source == 1 ? 0x000000u : (g.source == 2 ? g.rulerColor : 0xFFFFFFu));
        if (!b) {
            g.missing = true;
            return false;
        }
        g.bmp = b;
        g.srcW = kRulerW;
        g.srcH = kRulerH;
        g.missing = false;
        return true;
    }
    g.missing = true;
    if (g.path.empty()) return false;
    if (!ImgLoadFile(i, g.path)) return false;
    g.missing = false;
    return true;
}

static bool ImgIsPlaceholder(const ImgGroup& g) { return g.missing || !g.bmp; }

// 旋轉後、縮放比例 100% 時的大小；占位框使用固定大小
static void ImgBaseSize(int i, int* bw, int* bh) {
    const ImgGroup& g = g_img[i];
    if (ImgIsPlaceholder(g)) {
        *bw = kImgPlaceholderW;
        *bh = kImgPlaceholderH;
        return;
    }
    int w = g.srcW, h = g.srcH;
    if (g.rot == 90 || g.rot == 270) std::swap(w, h);
    *bw = std::max(1, w);
    *bh = std::max(1, h);
}

static void ImgDispSize(int i, int* w, int* h) {
    const ImgGroup& g = g_img[i];
    int bw, bh;
    ImgBaseSize(i, &bw, &bh);
    if (ImgIsPlaceholder(g)) {
        *w = bw;
        *h = bh;
        return;
    }
    *w = std::max(1, MulDiv(bw, g.scale, 100));
    *h = std::max(1, MulDiv(bh, g.scale, 100));
}

// 縮放比例下限：避免縮到看不見 (短邊至少 4 像素、長邊至少 24 像素，而且不低於 10%)
static int ImgMinScale(int i) {
    int bw, bh;
    ImgBaseSize(i, &bw, &bh);
    long long sh = std::min(bw, bh), lg = std::max(bw, bh);
    long long a = (100LL * kImgMinShort + sh - 1) / sh;
    long long b = (100LL * kImgMinLong + lg - 1) / lg;
    long long m = std::max<long long>(10, std::max(a, b));
    return (int)std::min<long long>(m, 100);   // 100% 一定允許
}

// 縮放比例上限：1000%，且縮放後的邊長與像素數不超過上限
static int ImgMaxScale(int i) {
    int bw, bh;
    ImgBaseSize(i, &bw, &bh);
    long long lg = std::max(bw, bh);
    long long m = 1000;
    m = std::min<long long>(m, 100LL * kImgMaxSide / lg);
    m = std::min<long long>(m, (long long)(std::sqrt((double)kImgMaxPixels / ((double)bw * (double)bh)) * 100.0));
    return (int)std::max<long long>(m, ImgMinScale(i));
}

static POINT ImgScreenPos(int i) {
    const ImgGroup& g = g_img[i];
    RECT mon = MonitorRectByName(g.monitor);
    POINT p;
    p.x = mon.left + g.x;
    p.y = mon.top + g.y;
    return p;
}

// 修正縮放比例與位置：圖片 (縮放後) 必須完整位於所在螢幕內；圖片本身 (100%) 比螢幕大時不限制位置
static void ImgClamp(int i) {
    ImgGroup& g = g_img[i];
    bool ph = ImgIsPlaceholder(g);
    int mn = ImgMinScale(i), mx = ImgMaxScale(i);
    if (!ph) g.scale = std::max(mn, std::min(mx, g.scale));
    RECT mon = MonitorRectByName(g.monitor);
    int mw = mon.right - mon.left, mh = mon.bottom - mon.top;
    int bw, bh;
    ImgBaseSize(i, &bw, &bh);
    if (bw > mw || bh > mh) return;
    if (!ph) {
        int fit = (int)std::min<long long>(100LL * mw / bw, 100LL * mh / bh);
        if (g.scale > fit) g.scale = std::max(mn, fit);
    }
    int dw, dh;
    ImgDispSize(i, &dw, &dh);
    if (dw <= mw) g.x = std::max(0, std::min(g.x, mw - dw));
    if (dh <= mh) g.y = std::max(0, std::min(g.y, mh - dh));
}

static std::wstring ImgFileName(const std::wstring& p) {
    size_t k = p.find_last_of(L"\\/");
    return (k == std::wstring::npos) ? p : p.substr(k + 1);
}

// 繪製：以 GDI+ 畫到 32bpp 預乘 Alpha 的 DIB，再用 UpdateLayeredWindow 更新視窗。
// fast = true (拖曳縮放中) 使用較快的內插方式。
static void ImgRender(int i, bool fast) {
    ImgGroup& g = g_img[i];
    if (!g.hwnd) return;
    int dw, dh;
    ImgDispSize(i, &dw, &dh);
    bool unlocked = !ImgIsLocked(i);
    int pad = unlocked ? kImgPad : 0;
    int ww = dw + 2 * pad, wh = dh + 2 * pad;
    if (!g.dc) {
        HDC sdc = GetDC(NULL);
        g.dc = CreateCompatibleDC(sdc);
        ReleaseDC(NULL, sdc);
        if (!g.dc) return;
    }
    if (!g.dib || g.dibW != ww || g.dibH != wh) {
        if (g.dib) {
            SelectObject(g.dc, g.oldBmp);
            DeleteObject(g.dib);
            g.dib = NULL;
            g.bits = NULL;
        }
        void* bits = NULL;
        g.dib = CreateDib32(g.dc, ww, wh, &bits);
        if (!g.dib || !bits) {
            if (g.dib) DeleteObject(g.dib);
            g.dib = NULL;
            g.bits = NULL;
            g.dibW = g.dibH = 0;
            return;
        }
        g.bits = bits;
        g.oldBmp = SelectObject(g.dc, g.dib);
        g.dibW = ww;
        g.dibH = wh;
    }
    {
        Gdiplus::Bitmap target(ww, wh, ww * 4, PixelFormat32bppPARGB, (BYTE*)g.bits);
        Gdiplus::Graphics gfx(&target);
        gfx.Clear(Gdiplus::Color(0, 0, 0, 0));
        gfx.SetCompositingMode(Gdiplus::CompositingModeSourceOver);
        if (unlocked) {   // 半透明深色背景
            Gdiplus::SolidBrush bgb(Gdiplus::Color(150, 20, 20, 20));
            gfx.FillRectangle(&bgb, 0, 0, ww, wh);
        }
        if (ImgIsPlaceholder(g)) {   // 圖片遺失 / 尚未選擇：占位框 + 提示文字
            Gdiplus::SolidBrush pb(Gdiplus::Color(215, 110, 25, 25));
            gfx.FillRectangle(&pb, pad, pad, dw, dh);
            Gdiplus::Pen pp(Gdiplus::Color(255, 255, 200, 0), 1.0f);
            gfx.DrawRectangle(&pp, pad, pad, dw - 1, dh - 1);
            std::wstring l1;
            if (g.source == 3 && !g.path.empty()) {
                std::wstring fn = ImgFileName(g.path);
                if (fn.size() > 100) fn.resize(100);
                wchar_t tb[300];
                wsprintfW(tb, T(S_IMG_MISSING), fn.c_str());
                l1 = tb;
            } else {
                l1 = T(S_IMG_NOTSET);
            }
            std::wstring text = l1 + L"\n" + T(S_IMG_MISSING2);
            Gdiplus::Font font(L"Segoe UI", 12.0f, Gdiplus::FontStyleRegular, Gdiplus::UnitPixel);
            Gdiplus::StringFormat sf;
            sf.SetAlignment(Gdiplus::StringAlignmentCenter);
            sf.SetLineAlignment(Gdiplus::StringAlignmentCenter);
            Gdiplus::SolidBrush tbr(Gdiplus::Color(255, 255, 255, 255));
            gfx.SetTextRenderingHint(Gdiplus::TextRenderingHintAntiAliasGridFit);
            Gdiplus::RectF rc((Gdiplus::REAL)(pad + 4), (Gdiplus::REAL)(pad + 2), (Gdiplus::REAL)(dw - 8), (Gdiplus::REAL)(dh - 4));
            gfx.DrawString(text.c_str(), -1, &font, rc, &sf, &tbr);
        } else {
            if (g.frames > 1) {
                GUID tm = Gdiplus::FrameDimensionTime;
                g.bmp->SelectActiveFrame(&tm, (UINT)g.frame);
            }
            Gdiplus::InterpolationMode im = Gdiplus::InterpolationModeHighQualityBicubic;
            if (g.scale == 100 || (g.source != 3 && g.scale % 100 == 0)) im = Gdiplus::InterpolationModeNearestNeighbor;   // 整數倍：維持像素的銳利
            else if (fast) im = Gdiplus::InterpolationModeBilinear;
            gfx.SetInterpolationMode(im);
            gfx.SetPixelOffsetMode(Gdiplus::PixelOffsetModeHalf);
            Gdiplus::ImageAttributes ia;
            ia.SetWrapMode(Gdiplus::WrapModeTileFlipXY);   // 縮放時避免邊緣出現半透明的框
            if (g.opacity < 100) {   // 不透明度：與圖片本身的 Alpha 相乘
                Gdiplus::ColorMatrix cm;
                ZeroMemory(&cm, sizeof(cm));
                for (int k = 0; k < 5; ++k) cm.m[k][k] = 1.0f;
                cm.m[3][3] = (Gdiplus::REAL)g.opacity / 100.0f;
                ia.SetColorMatrix(&cm, Gdiplus::ColorMatrixFlagsDefault, Gdiplus::ColorAdjustTypeBitmap);
            }
            // 以平行四邊形的三個頂點 (來源的左上 / 右上 / 左下) 表示旋轉與翻轉
            int xl = pad, yt = pad, xr = pad + dw, yb = pad + dh;
            Gdiplus::Point ul, ur, ll;
            switch (g.rot) {
            case 90:  ul = Gdiplus::Point(xr, yt); ur = Gdiplus::Point(xr, yb); ll = Gdiplus::Point(xl, yt); break;
            case 180: ul = Gdiplus::Point(xr, yb); ur = Gdiplus::Point(xl, yb); ll = Gdiplus::Point(xr, yt); break;
            case 270: ul = Gdiplus::Point(xl, yb); ur = Gdiplus::Point(xl, yt); ll = Gdiplus::Point(xr, yb); break;
            default:  ul = Gdiplus::Point(xl, yt); ur = Gdiplus::Point(xr, yt); ll = Gdiplus::Point(xl, yb); break;
            }
            if (g.flipH) {
                ul.X = xl + xr - ul.X;
                ur.X = xl + xr - ur.X;
                ll.X = xl + xr - ll.X;
            }
            Gdiplus::Point pts[3] = { ul, ur, ll };
            gfx.DrawImage(g.bmp, pts, 3, 0, 0, g.srcW, g.srcH, Gdiplus::UnitPixel, &ia);
        }
        if (unlocked) {   // 圖片外框 + 四角縮放控制點
            Gdiplus::Pen op(Gdiplus::Color(220, 255, 255, 255), 1.0f);
            gfx.DrawRectangle(&op, pad - 1, pad - 1, dw + 1, dh + 1);
            Gdiplus::SolidBrush hb(Gdiplus::Color(235, 255, 255, 255));
            Gdiplus::Pen hp(Gdiplus::Color(255, 40, 40, 40), 1.0f);
            int hx[4] = { 0, pad + dw, 0, pad + dw };
            int hy[4] = { 0, 0, pad + dh, pad + dh };
            for (int k = 0; k < 4; ++k) {
                gfx.FillRectangle(&hb, hx[k], hy[k], pad, pad);
                gfx.DrawRectangle(&hp, hx[k], hy[k], pad - 1, pad - 1);
            }
        }
        gfx.Flush(Gdiplus::FlushIntentionSync);
    }
    POINT sp = ImgScreenPos(i);
    POINT pos;
    pos.x = sp.x - pad;
    pos.y = sp.y - pad;
    SIZE size;
    size.cx = ww;
    size.cy = wh;
    POINT src;
    src.x = 0;
    src.y = 0;
    BLENDFUNCTION bf;
    bf.BlendOp = AC_SRC_OVER;
    bf.BlendFlags = 0;
    bf.SourceConstantAlpha = 255;
    bf.AlphaFormat = AC_SRC_ALPHA;
    HDC sdc = GetDC(NULL);
    UpdateLayeredWindow(g.hwnd, sdc, &pos, &size, g.dc, &src, 0, &bf, ULW_ALPHA);
    ReleaseDC(NULL, sdc);
}

static void ImgPlaceWindow(int i) {
    ImgGroup& g = g_img[i];
    if (!g.hwnd) return;
    int pad = ImgIsLocked(i) ? 0 : kImgPad;
    POINT p = ImgScreenPos(i);
    SetWindowPos(g.hwnd, NULL, p.x - pad, p.y - pad, 0, 0, SWP_NOSIZE | SWP_NOZORDER | SWP_NOACTIVATE);
}

// GIF：依影格的顯示時間與播放速度排下一次更新 (每次 WM_TIMER 後重新排)。隱藏 / 暫停 / 靜態圖片不使用計時器
static void ImgSchedule(int i) {
    ImgGroup& g = g_img[i];
    if (!g.hwnd) return;
    KillTimer(g.hwnd, 1);
    if (g.frames > 1 && !g.delays.empty() && g.bmp && !g.missing && !g.gifPaused && g.shown) {
        int d = g.delays[(size_t)g.frame % g.delays.size()];
        int ms = std::max(20, (int)((long long)d * 100 / std::max(10, g.gifSpeed)));
        SetTimer(g.hwnd, 1, (UINT)ms, NULL);
    }
}

static bool ImgCovered(HWND me) {
    RECT mr;
    if (!me || !GetWindowRect(me, &mr)) return false;
    DWORD gp = g_gamePid;
    int guard = 0;
    for (HWND w = GetWindow(me, GW_HWNDPREV); w && guard < 300; w = GetWindow(w, GW_HWNDPREV), ++guard) {
        if (!IsWindowVisible(w)) continue;
        RECT r, inter;
        if (!GetWindowRect(w, &r) || !IntersectRect(&inter, &mr, &r)) continue;
        DWORD pid = 0;
        GetWindowThreadProcessId(w, &pid);
        if (IsTaskbarClass(w) || (gp && pid == gp)) return true;
    }
    return false;
}

// 依層級由低到高重新置頂 (最後一個在最上面)
static void ImgRaiseAll() {
    int order[kImgGroups];
    ImgZOrder(order);
    for (int k = 0; k < kImgGroups; ++k) {
        ImgGroup& g = g_img[order[k]];
        if (g.hwnd && g.shown) SetWindowPos(g.hwnd, HWND_TOPMOST, 0, 0, 0, 0, SWP_NOMOVE | SWP_NOSIZE | SWP_NOACTIVATE);
    }
}

// 有圖片顯示時，每 100 毫秒檢查一次有沒有被工作列 / 遊戲視窗蓋住，被蓋住才重新置頂；沒有圖片顯示就不需要計時器
static void ImgCoverTimer() {
    bool any = false;
    for (int i = 0; i < kImgGroups; ++i) {
        if (g_img[i].hwnd && g_img[i].shown) any = true;
    }
    if (!g_hWnd) return;
    if (any) SetTimer(g_hWnd, 9, 100, NULL);
    else KillTimer(g_hWnd, 9);
}

static void ImgCheckCovered() {
    for (int i = 0; i < kImgGroups; ++i) {
        if (g_img[i].hwnd && g_img[i].shown && ImgCovered(g_img[i].hwnd)) {
            ImgRaiseAll();
            return;
        }
    }
}

// 鎖定：整個視窗滑鼠穿透且不會被啟動 (不搶遊戲的焦點)；未鎖定：可以點選 / 拖曳，點選後可用方向鍵微調
static void ImgApplyStyle(int i) {
    ImgGroup& g = g_img[i];
    if (!g.hwnd) return;
    LONG_PTR ex = GetWindowLongPtrW(g.hwnd, GWL_EXSTYLE);
    LONG_PTR want = ex;
    if (ImgIsLocked(i)) want |= (WS_EX_TRANSPARENT | WS_EX_NOACTIVATE);
    else want &= ~(LONG_PTR)(WS_EX_TRANSPARENT | WS_EX_NOACTIVATE);
    if (want != ex) SetWindowLongPtrW(g.hwnd, GWL_EXSTYLE, want);
}

static void ImgSetShown(int i, bool show) {
    ImgGroup& g = g_img[i];
    if (!g.hwnd) return;
    if (show && !g.shown) {
        ImgRender(i, false);
        ShowWindow(g.hwnd, SW_SHOWNA);
        g.shown = true;
        ImgRaiseAll();
        ImgSchedule(i);
    } else if (!show && g.shown) {
        KillTimer(g.hwnd, 1);
        ShowWindow(g.hwnd, SW_HIDE);
        g.shown = false;
    }
    ImgCoverTimer();
}

// 這一組現在是否該顯示：總開關 + 啟用；「僅在遊戲視窗為前景時顯示」時，前景是本工具 (選單 / 設定視窗 / 圖片本身) 或工作列則維持目前狀態
static bool ImgWantShow(int i) {
    const ImgGroup& g = g_img[i];
    if (!g_imgMaster || !g.enabled) return false;
    if (!g.fgOnly) return true;
    DWORD gp = g_gamePid;
    if (!gp) return false;
    HWND fg = GetForegroundWindow();
    DWORD fgPid = 0;
    if (fg) GetWindowThreadProcessId(fg, &fgPid);
    if (fg && (fgPid == GetCurrentProcessId() || IsTaskbarClass(fg))) return g.shown;
    return fgPid == gp;
}

static void ImgUpdateVisibility() {
    for (int i = 0; i < kImgGroups; ++i) {
        ImgGroup& g = g_img[i];
        if (!g.hwnd) continue;
        bool want = ImgWantShow(i);
        if (want != g.shown) ImgSetShown(i, want);
    }
}

static void ImgDestroy(int i) {
    ImgGroup& g = g_img[i];
    if (g.hwnd) {
        KillTimer(g.hwnd, 1);
        if (GetCapture() == g.hwnd) ReleaseCapture();
        HWND h = g.hwnd;
        g.hwnd = NULL;
        DestroyWindow(h);
    }
    g.shown = false;
    ImgFreeImage(i);
    ImgFreeDib(i);
    ImgCoverTimer();
}

struct ImgDragState {
    int idx, mode;   // mode：0 = 沒有拖曳，1 = 移動，2 = 縮放
    POINT cur0, abs0, anchor;
    int sx, sy;
    std::wstring mon;
    RECT monRc;
};
static ImgDragState g_imgDrag;

// 視窗內的位置落在哪個控制點：0 = 左上，1 = 右上，2 = 左下，3 = 右下，-1 = 不在控制點上
static int ImgHitCorner(int px, int py, int w, int h) {
    if (px < kImgPad && py < kImgPad) return 0;
    if (px >= w - kImgPad && py < kImgPad) return 1;
    if (px < kImgPad && py >= h - kImgPad) return 2;
    if (px >= w - kImgPad && py >= h - kImgPad) return 3;
    return -1;
}

static LRESULT CALLBACK ImgProc(HWND hwnd, UINT msg, WPARAM wp, LPARAM lp) {
    if (msg == WM_NCCREATE) {
        SetWindowLongPtrW(hwnd, GWLP_USERDATA, (LONG_PTR)((CREATESTRUCTW*)lp)->lpCreateParams);
        return DefWindowProcW(hwnd, msg, wp, lp);
    }
    int i = (int)GetWindowLongPtrW(hwnd, GWLP_USERDATA) - 1;
    if (i < 0 || i >= kImgGroups || g_img[i].hwnd != hwnd) return DefWindowProcW(hwnd, msg, wp, lp);
    ImgGroup& g = g_img[i];
    switch (msg) {
    case WM_NCHITTEST:
        return HTCLIENT;
    case WM_MOUSEACTIVATE:
        return ImgIsLocked(i) ? MA_NOACTIVATE : MA_ACTIVATE;
    case WM_ERASEBKGND:
        return 1;
    case WM_SETCURSOR:
        if (!ImgIsLocked(i)) {
            POINT p;
            GetCursorPos(&p);
            ScreenToClient(hwnd, &p);
            RECT cr;
            GetClientRect(hwnd, &cr);
            int corner = ImgIsPlaceholder(g) ? -1 : ImgHitCorner(p.x, p.y, cr.right, cr.bottom);
            int cur = 32646;   // IDC_SIZEALL
            if (corner == 0 || corner == 3) cur = 32642;   // IDC_SIZENWSE
            else if (corner == 1 || corner == 2) cur = 32643;   // IDC_SIZENESW
            SetCursor(LoadCursor(NULL, MAKEINTRESOURCE(cur)));
            return TRUE;
        }
        break;
    case WM_LBUTTONDOWN: {
        if (ImgIsLocked(i)) return 0;
        POINT c;
        GetCursorPos(&c);
        RECT cr;
        GetClientRect(hwnd, &cr);
        int corner = ImgIsPlaceholder(g) ? -1 : ImgHitCorner((short)LOWORD(lp), (short)HIWORD(lp), cr.right, cr.bottom);
        SetForegroundWindow(hwnd);   // 取得鍵盤焦點 (方向鍵微調)
        SetFocus(hwnd);
        POINT p = ImgScreenPos(i);
        int dw, dh;
        ImgDispSize(i, &dw, &dh);
        g_imgDrag.idx = i;
        g_imgDrag.cur0 = c;
        if (corner >= 0) {
            g_imgDrag.mode = 2;
            g_imgDrag.sx = (corner == 1 || corner == 3) ? 1 : -1;
            g_imgDrag.sy = (corner >= 2) ? 1 : -1;
            g_imgDrag.anchor.x = (g_imgDrag.sx > 0) ? p.x : p.x + dw;   // 對角的角落固定不動
            g_imgDrag.anchor.y = (g_imgDrag.sy > 0) ? p.y : p.y + dh;
            g_imgDrag.mon = g.monitor;
            g_imgDrag.monRc = MonitorRectByName(g.monitor);
        } else {
            g_imgDrag.mode = 1;
            g_imgDrag.abs0 = p;
        }
        SetCapture(hwnd);
        return 0;
    }
    case WM_MOUSEMOVE: {
        if (!g_imgDrag.mode || g_imgDrag.idx != i) break;
        POINT c;
        GetCursorPos(&c);
        if (g_imgDrag.mode == 1) {
            LONG ax = g_imgDrag.abs0.x + (c.x - g_imgDrag.cur0.x);
            LONG ay = g_imgDrag.abs0.y + (c.y - g_imgDrag.cur0.y);
            int dw, dh;
            ImgDispSize(i, &dw, &dh);
            POINT ctr;
            ctr.x = ax + dw / 2;
            ctr.y = ay + dh / 2;
            HMONITOR hm = MonitorFromPoint(ctr, MONITOR_DEFAULTTONEAREST);   // 以圖片中心所在的螢幕為準
            MONITORINFOEXW mi;
            ZeroMemory(&mi, sizeof(mi));
            mi.cbSize = sizeof(mi);
            if (GetMonitorInfoW(hm, (MONITORINFO*)&mi)) {
                g.monitor = mi.szDevice;
                g.x = (int)(ax - mi.rcMonitor.left);
                g.y = (int)(ay - mi.rcMonitor.top);
            }
            ImgClamp(i);
            ImgPlaceWindow(i);
        } else {
            // 等比例縮放：把游標相對於對角的位移，投影到圖片的對角線方向，換算成縮放比例
            int bw, bh;
            ImgBaseSize(i, &bw, &bh);
            double vx = (double)(c.x - g_imgDrag.anchor.x) * g_imgDrag.sx;
            double vy = (double)(c.y - g_imgDrag.anchor.y) * g_imgDrag.sy;
            double s = (vx * bw + vy * bh) / ((double)bw * bw + (double)bh * bh);
            int ns = (int)std::floor(s * 100.0 + 0.5);
            ns = std::max(ImgMinScale(i), std::min(ImgMaxScale(i), ns));
            const RECT& mr = g_imgDrag.monRc;
            int mw = mr.right - mr.left, mh = mr.bottom - mr.top;
            if (bw <= mw && bh <= mh) {   // 受限制時，縮放不得超出螢幕範圍
                long long roomW = (g_imgDrag.sx > 0) ? (mr.right - g_imgDrag.anchor.x) : (g_imgDrag.anchor.x - mr.left);
                long long roomH = (g_imgDrag.sy > 0) ? (mr.bottom - g_imgDrag.anchor.y) : (g_imgDrag.anchor.y - mr.top);
                long long fit = std::min(roomW * 100 / bw, roomH * 100 / bh);
                if (ns > fit) ns = (int)std::max<long long>(ImgMinScale(i), fit);
            }
            g.scale = ns;
            int dw, dh;
            ImgDispSize(i, &dw, &dh);
            int nx = (g_imgDrag.sx > 0) ? g_imgDrag.anchor.x : g_imgDrag.anchor.x - dw;
            int ny = (g_imgDrag.sy > 0) ? g_imgDrag.anchor.y : g_imgDrag.anchor.y - dh;
            g.monitor = g_imgDrag.mon;
            g.x = nx - mr.left;
            g.y = ny - mr.top;
            ImgClamp(i);
            ImgRender(i, true);
        }
        return 0;
    }
    case WM_LBUTTONUP:
    case WM_CAPTURECHANGED:
        if (g_imgDrag.mode && g_imgDrag.idx == i) {
            int mode = g_imgDrag.mode;
            g_imgDrag.mode = 0;
            if (GetCapture() == hwnd) ReleaseCapture();
            if (mode == 2) ImgRender(i, false);   // 縮放結束：以正常品質重繪
            ImgSaveGeom(i);
            ImgNotifyDlg(i);
        }
        return 0;
    case WM_KEYDOWN: {   // 未鎖定時：方向鍵以 1 像素微調位置 (按住 Shift 為 10 像素)
        if (ImgIsLocked(i)) break;
        int step = (GetKeyState(VK_SHIFT) & 0x8000) ? 10 : 1;
        int dx = 0, dy = 0;
        if (wp == VK_LEFT) dx = -step;
        else if (wp == VK_RIGHT) dx = step;
        else if (wp == VK_UP) dy = -step;
        else if (wp == VK_DOWN) dy = step;
        else break;
        g.x += dx;
        g.y += dy;
        ImgClamp(i);
        ImgPlaceWindow(i);
        ImgSaveGeom(i);
        ImgNotifyDlg(i);
        return 0;
    }
    case WM_TIMER:
        if (wp == 1) {
            KillTimer(hwnd, 1);
            if (g.frames > 1 && g.shown) {
                g.frame = (g.frame + 1) % g.frames;
                ImgRender(i, false);
                ImgSchedule(i);
            }
            return 0;
        }
        break;
    }
    return DefWindowProcW(hwnd, msg, wp, lp);
}

static bool ImgEnsureWindow(int i) {
    ImgGroup& g = g_img[i];
    if (g.hwnd) return true;
    if (!g_imgClassReg) {
        WNDCLASSEXW wc;
        ZeroMemory(&wc, sizeof(wc));
        wc.cbSize = sizeof(wc);
        wc.lpfnWndProc = ImgProc;
        wc.hInstance = g_hInst;
        wc.lpszClassName = L"MabinogiClientManagerImage";
        RegisterClassExW(&wc);
        g_imgClassReg = true;
    }
    DWORD ex = WS_EX_LAYERED | WS_EX_TOPMOST | WS_EX_TOOLWINDOW;
    if (ImgIsLocked(i)) ex |= WS_EX_TRANSPARENT | WS_EX_NOACTIVATE;
    HWND h = CreateWindowExW(ex, L"MabinogiClientManagerImage", L"ClientManagerImage", WS_POPUP, 0, 0, 1, 1, NULL, NULL, g_hInst, (LPVOID)(INT_PTR)(i + 1));
    if (!h) return false;
    g.hwnd = h;
    g.shown = false;
    ExcludeFromPeek(h);
    return true;
}

// 把這一組的狀態 (啟用 / 顯示 / 鎖定 / 圖片 / 位置大小...) 套用到視窗。notify = true (使用者操作) 時，圖片載入失敗會提示
static void ImgSync(int i, bool notify) {
    ImgGroup& g = g_img[i];
    if (!(g.enabled && g_imgMaster)) {   // 不需要顯示的組別不保留視窗與圖片 (省記憶體)
        ImgDestroy(i);
        return;
    }
    if (!ImgEnsureGdip() || !ImgEnsureWindow(i)) return;
    if (!g.loaded || g.loadedSig != ImgSigOf(g)) {
        bool ok = ImgLoad(i);
        if (!ok && notify && !(g.source == 3 && g.path.empty())) {
            std::wstring p = g.path;
            if (p.size() > 600) p.resize(600);
            wchar_t b[1100];
            wsprintfW(b, T(S_IMG_LOADFAIL), i + 1, p.c_str());
            Notify(b);
        }
    }
    ImgClamp(i);
    ImgApplyStyle(i);
    if (g.shown) ImgRender(i, false);
    ImgSetShown(i, ImgWantShow(i));
    ImgSchedule(i);
}

static void ImgSyncAll() {
    for (int i = 0; i < kImgGroups; ++i) ImgSync(i, false);
    ImgUpdateVisibility();
    ImgRaiseAll();
}

static void ImgShutdown() {
    for (int i = 0; i < kImgGroups; ++i) ImgDestroy(i);
    if (g_hWnd) KillTimer(g_hWnd, 9);
    if (g_gdipOn) {
        Gdiplus::GdiplusShutdown(g_gdipToken);
        g_gdipOn = false;
    }
}

// 層級：把這一組移到指定的層級，原本在那個層級的組別換到這一組原本的層級
static void ImgSetZ(int i, int newZ) {
    if (newZ < 0 || newZ >= kImgGroups || g_img[i].z == newZ) return;
    int old = g_img[i].z;
    for (int j = 0; j < kImgGroups; ++j) {
        if (j != i && g_img[j].z == newZ) {
            g_img[j].z = old;
            SaveIntS(ImgSec(j), L"Z", old);
        }
    }
    g_img[i].z = newZ;
    SaveIntS(ImgSec(i), L"Z", newZ);
    ImgRaiseAll();
}

static bool ImgBrowse(HWND owner, std::wstring& path) {
    wchar_t file[MAX_PATH * 2];
    file[0] = 0;
    if (!path.empty()) lstrcpynW(file, path.c_str(), MAX_PATH * 2);
    std::wstring filter = T(S_IMG_FILTER);
    filter.push_back(L'\0');
    filter += L"*.jpg;*.jpeg;*.png;*.gif";
    filter.push_back(L'\0');
    filter.push_back(L'\0');
    OPENFILENAMEW ofn;
    ZeroMemory(&ofn, sizeof(ofn));
    ofn.lStructSize = sizeof(ofn);
    ofn.hwndOwner = owner;
    ofn.lpstrFilter = filter.c_str();
    ofn.lpstrFile = file;
    ofn.nMaxFile = MAX_PATH * 2;
    ofn.Flags = OFN_FILEMUSTEXIST | OFN_PATHMUSTEXIST | OFN_HIDEREADONLY | OFN_NOCHANGEDIR;
    if (!GetOpenFileNameW(&ofn)) return false;
    path = file;
    return true;
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

// 設定視窗的頁面 (左側選單)
enum SetPage { SP_WINDOW = 0, SP_PRIO, SP_CPU, SP_MON, SP_IMG, SP_OTHER, SP_ABOUT, SP_COUNT };
#define WM_SD_SELPAGE (WM_APP + 10)   // 切換到指定的頁面 (wp = 頁面)
#define WM_SD_IMGCHANGED (WM_APP + 11)   // 圖片置頂：圖片被拖曳 / 縮放 / 微調 (wp = 組別，-1 = 全部重新載入)

static const wchar_t* PrioName(int lv);
static const wchar_t* IoName(int lv);
static std::wstring CoreTypeText(int core);
static void HandleCommand(int id);

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
            SendMessageW(dlg, WM_SD_SELPAGE, (WPARAM)SP_MON, 0);   // 色碼在「效能監控」頁：先切換到該頁
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

static void TmplItemCls(std::vector<WORD>& v, DWORD style, short x, short y, short cx, short cy, WORD id, const wchar_t* cls, const wchar_t* text) {
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
    TmplStr(v, cls);    // 以名稱指定控制項類別 (例如 SysListView32)
    TmplStr(v, text);
    v.push_back(0);     // 沒有建立資料
}

// ---------------------------------------------------------------------------
//  設定視窗：左側選單 (sidebar) 依設定種類分類，右側顯示該類別的設定
//  類別：遊戲視窗 / 優先權 / 親和性 / CPU 限制 / 效能監控 / 其他 / 關於
//  按「套用」或「確定」才會變更 (效能監控頁的語意同以前：套用 = 立即變更監控畫面但不寫入 ini，確定 = 寫入 ini，取消 = 回復)
// ---------------------------------------------------------------------------
enum SetDlgIds {
    SD_NAV = 6001,
    SD_W_BORDERLESS, SD_W_LOCK, SD_W_LOCKSTYLE, SD_W_HIDETB, SD_W_RESET, SD_W_CLIP, SD_W_MARGIN, SD_W_CLIPBL,
    SD_P_CPU, SD_P_GPU, SD_P_IO, SD_P_ALL, SD_P_P, SD_P_PNOHT, SD_P_E, SD_P_AFF, SD_P_TIP,
    SD_C_ENABLE, SD_C_ECO, SD_C_COND, SD_C_RATIO,
    SD_O_DBL, SD_O_LANG,
    SD_AUTO_BASE = 6500     // 靜態文字 / 群組框的自動編號
};
enum { AB_LOG = 3001, AB_COPY, AB_PAUSE, AB_LINK };
enum ImgDlgIds {
    SD_I_MASTER = 6100, SD_I_LOCKALL, SD_I_SEL, SD_I_ENABLE, SD_I_LOCK, SD_I_NAME, SD_I_SRC, SD_I_PATH, SD_I_BROWSE,
    SD_I_OPACITY, SD_I_SCALE, SD_I_X, SD_I_Y, SD_I_W, SD_I_H, SD_I_FLIP, SD_I_ROT, SD_I_Z, SD_I_FGONLY, SD_I_GIFPAUSE, SD_I_GIFSPEED, SD_I_COLOR, SD_I_COLORSW, SD_I_RESETSIZE
};

static HWND g_setDlg = NULL;   // 設定視窗

// 非監控頁的設定值 (視窗上的內容 / 開啟或上次套用時的基準值)
struct SetVals {
    bool borderless, lock, hideTb, clip, clipBl, tip, cpuEnabled, eco;
    int lockStyle, margin, cpuPrio, gpuPrio, ioPrio, mode, ratio, dbl, lang;
    unsigned long long aff;
};

struct SetCtx : MonDlgCtx {
    SetVals base;                 // 開啟 / 上次套用時的值：只有和它不同的項目才會被套用，不會蓋掉在視窗外 (選單、連點圖示) 做的變更
    OvSettings monBase;           // 監控頁：開啟 / 上次套用時的值
    int page;
    int imgSel;                   // 圖片置頂頁：目前選擇的組別 (0 ~ 9)
    HBRUSH imgSw;                 // 圖片置頂頁：自訂顏色的色塊預覽用的筆刷
    bool reopen;                  // 變更語言後重新建立視窗
    std::vector<std::pair<WORD, int> > pageOf;   // 控制項 -> 所屬頁面 (-1 = 每頁都顯示)
    HFONT font;                   // 診斷記錄用的等寬字型
    HFONT linkFont;               // 連結用的底線字型
    bool paused;
    std::wstring lastLog;
};

// CPU 親和性清單顯示的遮罩：設定檔尚未設定時，顯示遊戲目前的實際值 (遊戲沒有執行時顯示全部核心)
static unsigned long long DialogAffMask() {
    unsigned long long m = g_cfgAffMask;
    if (m == 0) {
        std::vector<DWORD> pids = GetClientPids();
        if (!pids.empty()) {
            HANDLE h = OpenProcess(PROCESS_QUERY_INFORMATION | PROCESS_QUERY_LIMITED_INFORMATION, FALSE, pids[0]);
            if (h) {
                DWORD_PTR pm = 0, sm = 0;
                if (GetProcessAffinityMask(h, &pm, &sm)) m = (unsigned long long)pm;
                CloseHandle(h);
            }
        }
    }
    m &= (unsigned long long)g_maskAll;
    if (m == 0) m = (unsigned long long)g_maskAll;
    return m;
}

static SetVals CaptureSetVals() {
    SetVals v;
    v.borderless = g_borderless;
    v.lock = g_locked;
    v.hideTb = g_hideTaskbar;
    v.clip = g_mouseClip;
    v.clipBl = g_mouseClipBorderless;
    v.tip = g_showTip;
    v.cpuEnabled = g_cpuEnabled;
    v.eco = g_eco;
    v.lockStyle = g_lockStyle;
    v.margin = g_mouseClipMargin;
    v.cpuPrio = g_cfgCpuPrio;
    v.gpuPrio = g_cfgGpuPrio;
    v.ioPrio = g_cfgIoPrio;
    v.mode = g_mode;
    v.ratio = g_ratio;
    v.dbl = g_dblAction;
    v.lang = g_langSetting;
    v.aff = DialogAffMask();
    return v;
}

// 選取下拉選單中資料值為 value 的項目；沒有這個值時 (例如 ini 設成選單沒有的值) 多加一個項目保留原值
static void ComboSelectValue(HWND dlg, int id, int value, const std::wstring& labelIfMissing) {
    HWND cb = GetDlgItem(dlg, id);
    int n = (int)SendMessageW(cb, CB_GETCOUNT, 0, 0);
    for (int i = 0; i < n; ++i) {
        if ((int)SendMessageW(cb, CB_GETITEMDATA, (WPARAM)i, 0) == value) {
            SendMessageW(cb, CB_SETCURSEL, (WPARAM)i, 0);
            return;
        }
    }
    ComboAdd(dlg, id, labelIfMissing.c_str(), value);
    SendMessageW(cb, CB_SETCURSEL, (WPARAM)n, 0);
}

static void AffListSet(HWND lv, unsigned long long mask) {
    int n = (int)SendMessageW(lv, LVM_GETITEMCOUNT, 0, 0);
    for (int r = 0; r < n; ++r) {
        LVITEMW it;
        ZeroMemory(&it, sizeof(it));
        it.mask = LVIF_PARAM;
        it.iItem = r;
        if (!SendMessageW(lv, LVM_GETITEMW, 0, (LPARAM)&it)) continue;
        ListView_SetCheckState(lv, r, ((mask >> it.lParam) & 1) ? TRUE : FALSE);
    }
}

static unsigned long long AffListGet(HWND lv) {
    unsigned long long mask = 0;
    int n = (int)SendMessageW(lv, LVM_GETITEMCOUNT, 0, 0);
    for (int r = 0; r < n; ++r) {
        LVITEMW it;
        ZeroMemory(&it, sizeof(it));
        it.mask = LVIF_PARAM;
        it.iItem = r;
        if (!SendMessageW(lv, LVM_GETITEMW, 0, (LPARAM)&it)) continue;
        if (ListView_GetCheckState(lv, r)) mask |= (1ULL << it.lParam);
    }
    return mask;
}

// 把設定值顯示到視窗上
static void LoadSetVals(HWND dlg, const SetVals& v) {
    DlgSetChecked(dlg, SD_W_BORDERLESS, v.borderless);
    DlgSetChecked(dlg, SD_W_LOCK, v.lock);
    DlgSetChecked(dlg, SD_W_HIDETB, v.hideTb);
    DlgSetChecked(dlg, SD_W_CLIP, v.clip);
    DlgSetChecked(dlg, SD_W_CLIPBL, v.clipBl);
    ComboSelectValue(dlg, SD_W_LOCKSTYLE, v.lockStyle, L"?");
    SetDlgItemInt(dlg, SD_W_MARGIN, (UINT)v.margin, FALSE);
    ComboSelectValue(dlg, SD_P_CPU, v.cpuPrio, T(S_PRIO_UNSET));
    ComboSelectValue(dlg, SD_P_GPU, v.gpuPrio, T(S_PRIO_UNSET));
    ComboSelectValue(dlg, SD_P_IO, v.ioPrio, T(S_PRIO_UNSET));
    AffListSet(GetDlgItem(dlg, SD_P_AFF), v.aff);
    DlgSetChecked(dlg, SD_P_TIP, v.tip);
    DlgSetChecked(dlg, SD_C_ENABLE, v.cpuEnabled);
    DlgSetChecked(dlg, SD_C_ECO, v.eco);
    ComboSelectValue(dlg, SD_C_COND, v.mode, L"?");
    ComboSelectValue(dlg, SD_C_RATIO, v.ratio, ComboLabel(1, v.ratio));
    ComboSelectValue(dlg, SD_O_DBL, v.dbl, L"?");
    ComboSelectValue(dlg, SD_O_LANG, v.lang, L"?");
}

// 讀取視窗上的設定值 (讀不到的項目沿用基準值)
static void ReadSetVals(HWND dlg, const SetVals& base, SetVals& w) {
    w = base;
    w.borderless = DlgChecked(dlg, SD_W_BORDERLESS);
    w.lock = DlgChecked(dlg, SD_W_LOCK);
    w.hideTb = DlgChecked(dlg, SD_W_HIDETB);
    w.clip = DlgChecked(dlg, SD_W_CLIP);
    w.clipBl = DlgChecked(dlg, SD_W_CLIPBL);
    w.lockStyle = ComboValue(dlg, SD_W_LOCKSTYLE, base.lockStyle);
    BOOL ok = FALSE;
    UINT m = GetDlgItemInt(dlg, SD_W_MARGIN, &ok, FALSE);
    w.margin = ok ? (int)std::min<UINT>(m, 200) : base.margin;
    w.cpuPrio = ComboValue(dlg, SD_P_CPU, base.cpuPrio);
    w.gpuPrio = ComboValue(dlg, SD_P_GPU, base.gpuPrio);
    w.ioPrio = ComboValue(dlg, SD_P_IO, base.ioPrio);
    w.aff = AffListGet(GetDlgItem(dlg, SD_P_AFF));
    w.tip = DlgChecked(dlg, SD_P_TIP);
    w.cpuEnabled = DlgChecked(dlg, SD_C_ENABLE);
    w.eco = DlgChecked(dlg, SD_C_ECO);
    w.mode = ComboValue(dlg, SD_C_COND, base.mode);
    w.ratio = ComboValue(dlg, SD_C_RATIO, base.ratio);
    w.dbl = ComboValue(dlg, SD_O_DBL, base.dbl);
    w.lang = ComboValue(dlg, SD_O_LANG, base.lang);
}

// 套用非監控頁的設定：只處理和基準值 (b) 不同、而且和目前實際狀態不同的項目，直接沿用選單的處理流程。
// 回傳是否變更了語言。
static bool CommitSetVals(const SetVals& w, const SetVals& b) {
    // --- 遊戲視窗 ---
    if (w.lockStyle != b.lockStyle && w.lockStyle != g_lockStyle) {
        bool redo = g_locked && !GetGameWindows().empty();
        if (redo) HandleCommand(ID_LOCK);   // 先用舊的方式解除鎖定
        g_lockStyle = w.lockStyle;
        SaveInt(L"LockStyle", g_lockStyle);
        if (redo && !g_locked) HandleCommand(ID_LOCK);   // 再用新的方式鎖定
    }
    bool lockChange = (w.lock != b.lock && w.lock != g_locked);
    if (lockChange && !w.lock) HandleCommand(ID_LOCK);
    if (w.borderless != b.borderless && w.borderless != g_borderless) HandleCommand(ID_TOGGLE);
    if (lockChange && w.lock) HandleCommand(ID_LOCK);
    if (w.hideTb != b.hideTb && w.hideTb != g_hideTaskbar) HandleCommand(ID_HIDE_TASKBAR);
    bool clipOpt = false;
    if (w.margin != b.margin && w.margin != g_mouseClipMargin) {
        g_mouseClipMargin = w.margin;
        SaveInt(L"MouseClipMargin", g_mouseClipMargin);
        clipOpt = true;
    }
    if (w.clipBl != b.clipBl && w.clipBl != g_mouseClipBorderless) {
        g_mouseClipBorderless = w.clipBl;
        SaveInt(L"MouseClipBorderless", g_mouseClipBorderless ? 1 : 0);
        clipOpt = true;
    }
    if (w.clip != b.clip && w.clip != g_mouseClip) HandleCommand(ID_MOUSE_CLIP);
    else if (clipOpt && g_mouseClip) UpdateMouseClip();
    // --- 優先權 / 親和性 ---
    if (w.cpuPrio != b.cpuPrio && w.cpuPrio >= 1 && w.cpuPrio <= 6) HandleCommand(ID_PRIO_CPU_BASE + w.cpuPrio);
    if (w.gpuPrio != b.gpuPrio && w.gpuPrio >= 1 && w.gpuPrio <= 6) HandleCommand(ID_GPU_BASE + w.gpuPrio);
    if (w.ioPrio != b.ioPrio && w.ioPrio >= 1 && w.ioPrio <= 4) HandleCommand(ID_IO_BASE + w.ioPrio);
    if (w.aff != b.aff) {
        if (w.aff == 0) Notify(T(S_NEED_ONE_CORE));
        else SetAffMask(w.aff & (unsigned long long)g_maskAll);
    }
    if (w.tip != b.tip && w.tip != g_showTip) HandleCommand(ID_SHOWTIP);
    // --- CPU 限制 ---
    if (w.cpuEnabled != b.cpuEnabled && w.cpuEnabled != g_cpuEnabled) HandleCommand(ID_CPU_ENABLE);
    if (w.eco != b.eco && w.eco != g_eco) HandleCommand(ID_ECO);
    if (w.mode != b.mode && w.mode >= 1 && w.mode <= 3 && w.mode != g_mode) SetMode(w.mode);
    if (w.ratio != b.ratio && w.ratio >= 1 && w.ratio <= 99 && w.ratio != g_ratio) {
        g_ratio = w.ratio;
        SaveInt(L"Ratio", w.ratio);
        WakeEngine();
    }
    // --- 其他 ---
    if (w.dbl != b.dbl && w.dbl >= 0 && w.dbl <= 4 && w.dbl != g_dblAction) HandleCommand(ID_DBL_BASE + w.dbl);
    bool langChanged = false;
    if (w.lang != b.lang && w.lang >= UL_AUTO && w.lang <= UL_KO && w.lang != g_langSetting) {
        HandleCommand(ID_LANG_BASE + w.lang);
        langChanged = true;
    }
    return langChanged;
}

// 監控設定是否有變 (位置不算：位置由拖曳決定，不在視窗上編輯)
static bool OvEqual(const OvSettings& a, const OvSettings& b) {
    return a.cpu == b.cpu && a.cpuPct == b.cpuPct && a.cpuGhz == b.cpuGhz && a.ram == b.ram && a.ramPct == b.ramPct && a.ramMb == b.ramMb &&
           a.gpu == b.gpu && a.vram == b.vram && a.vramPct == b.vramPct && a.vramMb == b.vramMb && a.fps == b.fps && a.latency == b.latency &&
           a.enabled == b.enabled && a.fgOnly == b.fgOnly && a.locked == b.locked && a.lockNoBg == b.lockNoBg &&
           a.layout == b.layout && a.intervalMs == b.intervalMs && a.fontSize == b.fontSize && a.opacity == b.opacity &&
           a.cpuMethod == b.cpuMethod && a.latMethod == b.latMethod && a.textColor == b.textColor && a.outlineColor == b.outlineColor &&
           a.bgColor == b.bgColor && a.separator == b.separator && a.order == b.order;
}

// 套用期間暫時停用設定視窗：避免提示視窗 (例如「遊戲未啟動」) 開著時又按到「套用」
struct DlgDisable {
    HWND h;
    explicit DlgDisable(HWND d) : h(d) { EnableWindow(h, FALSE); }
    ~DlgDisable() { EnableWindow(h, TRUE); }
};

// 套用視窗上的所有設定。save = true (按「確定」) 時，監控設定也寫入 ini。
// 回傳 false = 內容有誤 (已提示)，視窗維持開啟。
static bool CommitSettings(HWND dlg, SetCtx* c, bool save, bool* langChanged) {
    *langChanged = false;
    OvSettings ms;
    if (!ReadMonDlg(dlg, ms)) return false;
    SetVals want;
    ReadSetVals(dlg, c->base, want);
    DlgDisable guard(dlg);
    if (!OvEqual(ms, c->monBase)) {
        ApplyOvSettings(ms);
        OverlayRefresh();   // 立即變更監控畫面，尚未寫入 ini
        c->monBase = ms;
    }
    if (save) SaveOverlaySettings();   // 按下確定才寫入 ini
    *langChanged = CommitSetVals(want, c->base);
    c->base = CaptureSetVals();
    LoadSetVals(dlg, c->base);
    return true;
}

// ---------------------------------------------------------------------------
//  圖片置頂頁：此頁的變更立即生效並寫入 ini (不經過下方的「確定 / 取消 / 套用」)；
//  圖片被拖曳 / 縮放 / 方向鍵微調後，ImgNotifyDlg 會通知這裡更新位置與大小欄位
// ---------------------------------------------------------------------------
static void ImgPageFillSel(HWND dlg, SetCtx* c) {
    HWND cb = GetDlgItem(dlg, SD_I_SEL);
    SendMessageW(cb, CB_RESETCONTENT, 0, 0);
    for (int k = 0; k < kImgGroups; ++k) {
        wchar_t b[64];
        wsprintfW(b, T(S_IMG_GROUPN), k + 1);
        std::wstring s = b;
        if (!g_img[k].name.empty()) {
            s += L" - ";
            s += g_img[k].name;
        }
        ComboAdd(dlg, SD_I_SEL, s.c_str(), k);
    }
    SendMessageW(cb, CB_SETCURSEL, (WPARAM)c->imgSel, 0);
}

// 只在內容不同時才更新欄位，避免打斷使用者正在輸入的欄位
static void ImgSetEditInt(HWND dlg, int id, int v, bool isSigned) {
    BOOL ok = FALSE;
    int cur = (int)GetDlgItemInt(dlg, id, &ok, isSigned ? TRUE : FALSE);
    if (ok && cur == v) return;
    SetDlgItemInt(dlg, id, (UINT)v, isSigned ? TRUE : FALSE);
}

static void ImgSetEditText(HWND dlg, int id, const std::wstring& s) {
    wchar_t b[1100];
    b[0] = 0;
    GetDlgItemTextW(dlg, id, b, 1100);
    if (s == b) return;
    SetDlgItemTextW(dlg, id, s.c_str());
}

static void ImgPageLoadGeom(HWND dlg, SetCtx* c) {
    int i = c->imgSel;
    const ImgGroup& g = g_img[i];
    int dw, dh;
    ImgDispSize(i, &dw, &dh);
    ImgSetEditInt(dlg, SD_I_OPACITY, g.opacity, false);
    ImgSetEditInt(dlg, SD_I_SCALE, g.scale, false);
    ImgSetEditInt(dlg, SD_I_X, g.x, true);
    ImgSetEditInt(dlg, SD_I_Y, g.y, true);
    ImgSetEditInt(dlg, SD_I_W, dw, false);
    ImgSetEditInt(dlg, SD_I_H, dh, false);
    bool ph = ImgIsPlaceholder(g);
    EnableWindow(GetDlgItem(dlg, SD_I_SCALE), !ph);
    EnableWindow(GetDlgItem(dlg, SD_I_W), !ph);
    EnableWindow(GetDlgItem(dlg, SD_I_H), !ph);
}

// 自訂顏色的色塊預覽：隨輸入即時更新，格式不對時顯示灰色
static void ImgUpdateSwatch(HWND dlg, SetCtx* c) {
    wchar_t b[32];
    b[0] = 0;
    GetDlgItemTextW(dlg, SD_I_COLOR, b, 32);
    bool ok = false;
    unsigned int v = ParseHexColor(b, 0, &ok);
    COLORREF col = ok ? RGB((v >> 16) & 0xFF, (v >> 8) & 0xFF, v & 0xFF) : RGB(200, 200, 200);
    if (c->imgSw) DeleteObject(c->imgSw);
    c->imgSw = CreateSolidBrush(col);
    InvalidateRect(GetDlgItem(dlg, SD_I_COLORSW), NULL, TRUE);
}

static void ImgPageLoad(HWND dlg, SetCtx* c) {
    int i = c->imgSel;
    const ImgGroup& g = g_img[i];
    DlgSetChecked(dlg, SD_I_MASTER, g_imgMaster);
    DlgSetChecked(dlg, SD_I_LOCKALL, g_imgLockAll);
    ImgPageFillSel(dlg, c);
    DlgSetChecked(dlg, SD_I_ENABLE, g.enabled);
    DlgSetChecked(dlg, SD_I_LOCK, g.locked);
    ImgSetEditText(dlg, SD_I_NAME, g.name);
    ComboSelectValue(dlg, SD_I_SRC, g.source, L"?");
    ImgSetEditText(dlg, SD_I_PATH, g.path);
    DlgSetChecked(dlg, SD_I_FLIP, g.flipH);
    ComboSelectValue(dlg, SD_I_ROT, g.rot, L"?");
    ComboSelectValue(dlg, SD_I_Z, g.z, L"?");
    DlgSetChecked(dlg, SD_I_FGONLY, g.fgOnly);
    DlgSetChecked(dlg, SD_I_GIFPAUSE, g.gifPaused);
    ComboSelectValue(dlg, SD_I_GIFSPEED, g.gifSpeed, ComboLabel(1, g.gifSpeed));
    ImgPageLoadGeom(dlg, c);
    // 白色 / 黑色時顯示實際使用的顏色 (只是顯示，不會寫入 RulerColor)；選回自訂顏色時恢復成使用者設定的值
    ImgSetEditText(dlg, SD_I_COLOR, HexColorText(g.source == 0 ? 0xFFFFFFu : (g.source == 1 ? 0x000000u : g.rulerColor)));
    ImgUpdateSwatch(dlg, c);
    EnableWindow(GetDlgItem(dlg, SD_I_COLOR), g.source == 2);
    bool file = (g.source == 3);
    EnableWindow(GetDlgItem(dlg, SD_I_PATH), file);
    EnableWindow(GetDlgItem(dlg, SD_I_BROWSE), file);
    bool anim = (g.frames > 1);   // GIF 設定只有動態圖片才能使用
    EnableWindow(GetDlgItem(dlg, SD_I_GIFPAUSE), anim);
    EnableWindow(GetDlgItem(dlg, SD_I_GIFSPEED), anim);
}

// 把輸入欄位的內容 (名稱 / 路徑 / 不透明度 / 縮放 / 位置 / 大小) 套用到目前選擇的組別；只處理和目前不同的欄位
static void ImgPageApplyEdits(HWND dlg, SetCtx* c) {
    int i = c->imgSel;
    ImgGroup& g = g_img[i];
    bool changed = false, nameChanged = false, pathChanged = false;
    wchar_t buf[1100];
    buf[0] = 0;
    GetDlgItemTextW(dlg, SD_I_NAME, buf, 41);
    if (g.name != buf) {
        g.name = buf;
        nameChanged = changed = true;
    }
    if (g.source == 3) {
        buf[0] = 0;
        GetDlgItemTextW(dlg, SD_I_PATH, buf, 1000);
        std::wstring p = buf;
        if (p.size() >= 2 && p.front() == L'"' && p.back() == L'"') p = p.substr(1, p.size() - 2);   // 貼上「複製為路徑」時會帶引號
        if (p != g.path) {
            g.path = p;
            pathChanged = changed = true;
        }
    }
    if (g.source == 2) {   // 自訂顏色：RRGGBB，格式不對時還原成目前的顏色
        buf[0] = 0;
        GetDlgItemTextW(dlg, SD_I_COLOR, buf, 16);
        bool cok = false;
        unsigned int cv = ParseHexColor(buf, g.rulerColor, &cok);
        if (!cok) {
            ImgSetEditText(dlg, SD_I_COLOR, HexColorText(g.rulerColor));
        } else if (cv != g.rulerColor) {
            g.rulerColor = cv;
            changed = true;
        }
    }
    BOOL ok = FALSE;
    UINT ov = GetDlgItemInt(dlg, SD_I_OPACITY, &ok, FALSE);
    if (ok) {
        int o = (int)std::max<UINT>(5, std::min<UINT>(100, ov));
        if (o != g.opacity) {
            g.opacity = o;
            changed = true;
        }
    }
    if (!ImgIsPlaceholder(g)) {
        int dw, dh, bw, bh;
        ImgDispSize(i, &dw, &dh);
        ImgBaseSize(i, &bw, &bh);
        UINT sc = GetDlgItemInt(dlg, SD_I_SCALE, &ok, FALSE);
        if (ok && (int)sc != g.scale) {
            g.scale = (int)std::min<UINT>(sc, 100000);
            changed = true;
        } else {
            UINT w = GetDlgItemInt(dlg, SD_I_W, &ok, FALSE);
            if (ok && (int)w != dw) {
                g.scale = (int)std::min<double>(100000.0, (double)w * 100.0 / bw + 0.5);   // 寬 / 高會維持圖片的長寬比
                changed = true;
            } else {
                UINT h = GetDlgItemInt(dlg, SD_I_H, &ok, FALSE);
                if (ok && (int)h != dh) {
                    g.scale = (int)std::min<double>(100000.0, (double)h * 100.0 / bh + 0.5);
                    changed = true;
                }
            }
        }
    }
    int xv = (int)GetDlgItemInt(dlg, SD_I_X, &ok, TRUE);
    if (ok && xv != g.x) {
        g.x = xv;
        changed = true;
    }
    int yv = (int)GetDlgItemInt(dlg, SD_I_Y, &ok, TRUE);
    if (ok && yv != g.y) {
        g.y = yv;
        changed = true;
    }
    if (!changed) return;
    ImgSaveAll(i);
    ImgSync(i, pathChanged);
    if (nameChanged) ImgPageFillSel(dlg, c);
    ImgPageLoad(dlg, c);   // 顯示修正後 (例如超出螢幕範圍) 的實際數值
}

// 處理圖片置頂頁的控制項；回傳 true = 已處理
static bool ImgPageCommand(HWND dlg, SetCtx* c, int id, int code) {
    if (id < SD_I_MASTER || id > SD_I_RESETSIZE) return false;
    int i = c->imgSel;
    ImgGroup& g = g_img[i];
    if (id == SD_I_COLOR && code == EN_CHANGE) {
        ImgUpdateSwatch(dlg, c);
        return true;
    }
    if (id == SD_I_COLORSW) return true;
    bool click = (code == BN_CLICKED);
    bool sel = (code == CBN_SELCHANGE);
    switch (id) {
    case SD_I_MASTER:
        if (click) {
            g_imgMaster = DlgChecked(dlg, id);
            SaveInt(L"ImgMaster", g_imgMaster ? 1 : 0);
            ImgSyncAll();
        }
        break;
    case SD_I_LOCKALL:
        if (click) {
            g_imgLockAll = DlgChecked(dlg, id);
            SaveInt(L"ImgLockAll", g_imgLockAll ? 1 : 0);
            ImgSyncAll();
        }
        break;
    case SD_I_SEL:
        if (sel) {
            ImgPageApplyEdits(dlg, c);   // 先套用上一組還沒套用的輸入
            c->imgSel = std::max(0, std::min(kImgGroups - 1, ComboValue(dlg, id, c->imgSel)));
            ImgPageLoad(dlg, c);
        }
        break;
    case SD_I_ENABLE:
        if (click) {
            g.enabled = DlgChecked(dlg, id);
            ImgSaveAll(i);
            ImgSync(i, true);
            ImgPageLoad(dlg, c);
        }
        break;
    case SD_I_LOCK:
        if (click) {
            g.locked = DlgChecked(dlg, id);
            ImgSaveAll(i);
            ImgSync(i, false);
        }
        break;
    case SD_I_SRC:
        if (sel) {
            g.source = ComboValue(dlg, id, g.source);
            ImgSaveAll(i);
            ImgSync(i, true);
            ImgPageLoad(dlg, c);
        }
        break;
    case SD_I_BROWSE:
        if (click) {
            std::wstring p = g.path;
            if (ImgBrowse(dlg, p)) {
                g.path = p;
                g.source = 3;
                ImgSaveAll(i);
                ImgSync(i, true);
                ImgPageLoad(dlg, c);
            }
        }
        break;
    case SD_I_FLIP:
        if (click) {
            g.flipH = DlgChecked(dlg, id);
            ImgSaveAll(i);
            ImgSync(i, false);
        }
        break;
    case SD_I_ROT:
        if (sel) {
            g.rot = ComboValue(dlg, id, g.rot);
            ImgSync(i, false);   // 旋轉 90 / 270 度時寬高互換，位置也會跟著修正
            ImgSaveAll(i);
            ImgPageLoadGeom(dlg, c);
        }
        break;
    case SD_I_Z:
        if (sel) ImgSetZ(i, ComboValue(dlg, id, g.z));
        break;
    case SD_I_FGONLY:
        if (click) {
            g.fgOnly = DlgChecked(dlg, id);
            ImgSaveAll(i);
            ImgSync(i, false);
        }
        break;
    case SD_I_GIFPAUSE:
        if (click) {
            g.gifPaused = DlgChecked(dlg, id);
            ImgSaveAll(i);
            ImgSchedule(i);
        }
        break;
    case SD_I_GIFSPEED:
        if (sel) {
            g.gifSpeed = ComboValue(dlg, id, g.gifSpeed);
            ImgSaveAll(i);
            ImgSchedule(i);
        }
        break;
    case SD_I_RESETSIZE:
        if (click) {
            g.scale = 100;
            ImgSync(i, false);
            ImgSaveAll(i);
            ImgPageLoadGeom(dlg, c);
        }
        break;
    default:   // 輸入欄位：離開欄位時套用
        if (code == EN_KILLFOCUS) ImgPageApplyEdits(dlg, c);
        break;
    }
    return true;
}

static void ImgPageInit(HWND dlg, SetCtx* c) {
    c->imgSel = 0;
    ComboAdd(dlg, SD_I_SRC, T(S_IMG_SRC_W), 0);
    ComboAdd(dlg, SD_I_SRC, T(S_IMG_SRC_B), 1);
    ComboAdd(dlg, SD_I_SRC, T(S_IMG_SRC_C), 2);
    ComboAdd(dlg, SD_I_SRC, T(S_IMG_SRC_F), 3);
    static const int rots[4] = { 0, 90, 180, 270 };
    for (int k = 0; k < 4; ++k) {
        wchar_t b[16];
        wsprintfW(b, L"%d\u00B0", rots[k]);
        ComboAdd(dlg, SD_I_ROT, b, rots[k]);
    }
    for (int k = 0; k < kImgGroups; ++k) {
        wchar_t b[16];
        wsprintfW(b, L"%d", k + 1);
        ComboAdd(dlg, SD_I_Z, b, k);
    }
    static const int speeds[] = { 25, 50, 75, 100, 150, 200, 300 };
    for (int k = 0; k < (int)(sizeof(speeds) / sizeof(speeds[0])); ++k) ComboAdd(dlg, SD_I_GIFSPEED, ComboLabel(1, speeds[k]).c_str(), speeds[k]);
    SendDlgItemMessageW(dlg, SD_I_COLOR, EM_LIMITTEXT, 7, 0);
    SendDlgItemMessageW(dlg, SD_I_NAME, EM_LIMITTEXT, 40, 0);
    SendDlgItemMessageW(dlg, SD_I_PATH, EM_LIMITTEXT, 1000, 0);
    SendDlgItemMessageW(dlg, SD_I_OPACITY, EM_LIMITTEXT, 3, 0);
    SendDlgItemMessageW(dlg, SD_I_SCALE, EM_LIMITTEXT, 5, 0);
    SendDlgItemMessageW(dlg, SD_I_W, EM_LIMITTEXT, 5, 0);
    SendDlgItemMessageW(dlg, SD_I_H, EM_LIMITTEXT, 5, 0);
    SendDlgItemMessageW(dlg, SD_I_X, EM_LIMITTEXT, 7, 0);
    SendDlgItemMessageW(dlg, SD_I_Y, EM_LIMITTEXT, 7, 0);
    ImgPageLoad(dlg, c);
}

static void ImgNotifyDlg(int idx) {
    if (g_setDlg) PostMessageW(g_setDlg, WM_SD_IMGCHANGED, (WPARAM)idx, 0);
}

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

static void UpdateAboutLog(HWND dlg, SetCtx* c) {
    if (!c || c->paused) return;
    HWND ed = GetDlgItem(dlg, AB_LOG);
    if (AboutLogBusy(ed)) return;
    std::wstring txt = BuildDebugText();
    if (txt != c->lastLog) {
        c->lastLog = txt;
        SetWindowTextW(ed, txt.c_str());
    }
}

// 切換頁面：只顯示該頁的控制項。效能監控頁開啟期間監控畫面固定顯示 (預覽)；
// 診斷記錄只在「關於」頁顯示期間收集 (不寫入檔案)。
static void SelectPage(HWND dlg, SetCtx* c, int page) {
    if (page < 0 || page >= SP_COUNT) page = 0;
    c->page = page;
    SendDlgItemMessageW(dlg, SD_NAV, LB_SETCURSEL, (WPARAM)page, 0);
    for (size_t i = 0; i < c->pageOf.size(); ++i) {
        if (c->pageOf[i].second < 0) continue;
        HWND h = GetDlgItem(dlg, c->pageOf[i].first);
        if (h) ShowWindow(h, c->pageOf[i].second == page ? SW_SHOWNA : SW_HIDE);
    }
    bool mon = (page == SP_MON), about = (page == SP_ABOUT);
    if (mon != g_monPreview) {
        g_monPreview = mon;
        OverlayRefresh();
    }
    if (about != g_ovDebug) {
        g_ovDebug = about;
        if (about) {
            ClearDebugText();
            if (g_monWake) SetEvent(g_monWake);
            UpdateAboutLog(dlg, c);
        }
    }
}

// 效能監控頁：以目前的監控設定初始化控制項
static void MonPageInit(HWND dlg, SetCtx* c) {
    const OvSettings& s = c->monBase;
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
}

static void SetupSettingsDlg(HWND dlg, SetCtx* c) {
    // 左側選單
    static const int navText[SP_COUNT] = { S_CAT_WINDOW, S_CAT_PRIO, S_CAT_CPU, S_M_MON, S_M_IMG, S_CAT_OTHER, S_ABOUT_TITLE };
    for (int i = 0; i < SP_COUNT; ++i) SendDlgItemMessageW(dlg, SD_NAV, LB_ADDSTRING, 0, (LPARAM)T(navText[i]));
    // 遊戲視窗
    ComboAdd(dlg, SD_W_LOCKSTYLE, T(S_LOCKSTYLE_0), 0);
    ComboAdd(dlg, SD_W_LOCKSTYLE, T(S_LOCKSTYLE_1), 1);
    SendDlgItemMessageW(dlg, SD_W_MARGIN, EM_LIMITTEXT, 3, 0);
    // 優先權 / 親和性 (由高到低)
    for (int lv = 6; lv >= 1; --lv) {
        ComboAdd(dlg, SD_P_CPU, PrioName(lv), lv);
        ComboAdd(dlg, SD_P_GPU, PrioName(lv), lv);
    }
    for (int lv = 4; lv >= 1; --lv) ComboAdd(dlg, SD_P_IO, IoName(lv), lv);
    {
        HWND lv = GetDlgItem(dlg, SD_P_AFF);
        ListView_SetExtendedListViewStyle(lv, LVS_EX_CHECKBOXES | LVS_EX_FULLROWSELECT);
        RECT rc;
        GetClientRect(lv, &rc);
        LVCOLUMNW col;
        ZeroMemory(&col, sizeof(col));
        col.mask = LVCF_WIDTH;
        col.cx = std::max<int>(50, (int)rc.right - GetSystemMetrics(SM_CXVSCROLL) - 4);
        SendMessageW(lv, LVM_INSERTCOLUMNW, 0, (LPARAM)&col);
        int row = 0;
        for (int i = 0; i < g_coreCount && i < 64; ++i) {
            if (!((g_maskAll >> i) & 1)) continue;
            wchar_t label[200];
            std::wstring ct = CoreTypeText(i);
            wsprintfW(label, T(S_CORE_ITEM), i, ct.c_str());
            LVITEMW it;
            ZeroMemory(&it, sizeof(it));
            it.mask = LVIF_TEXT | LVIF_PARAM;
            it.iItem = row;
            it.pszText = label;
            it.lParam = i;
            SendMessageW(lv, LVM_INSERTITEMW, 0, (LPARAM)&it);
            ++row;
        }
    }
    // CPU 限制
    ComboAdd(dlg, SD_C_COND, T(S_C_ALWAYS), 1);
    ComboAdd(dlg, SD_C_COND, T(S_C_MIN), 2);
    ComboAdd(dlg, SD_C_COND, T(S_C_BG), 3);
    for (int i = 0; i < kRatioCount; ++i) ComboAdd(dlg, SD_C_RATIO, ComboLabel(1, kRatios[i]).c_str(), kRatios[i]);
    // 其他
    ComboAdd(dlg, SD_O_DBL, T(S_DBL_SETTINGS), 0);
    ComboAdd(dlg, SD_O_DBL, T(S_M_TOGGLE), 1);
    ComboAdd(dlg, SD_O_DBL, T(S_DBL_CPU), 2);
    ComboAdd(dlg, SD_O_DBL, T(S_DBL_MON), 3);
    ComboAdd(dlg, SD_O_DBL, T(S_DBL_TASKBAR), 4);
    ComboAdd(dlg, SD_O_LANG, T(S_L_AUTO), UL_AUTO);
    for (int l = UL_ZHTW; l <= UL_KO; ++l) ComboAdd(dlg, SD_O_LANG, LangLabel(l), l);
    LoadSetVals(dlg, c->base);
    MonPageInit(dlg, c);
    ImgPageInit(dlg, c);
    // 關於：診斷記錄用等寬字型、連結用底線字型
    c->font = CreateFontW(-MulDiv(9, OverlayDpi(), 72), 0, 0, 0, FW_NORMAL, FALSE, FALSE, FALSE, DEFAULT_CHARSET,
                          OUT_DEFAULT_PRECIS, CLIP_DEFAULT_PRECIS, DEFAULT_QUALITY, FIXED_PITCH | FF_MODERN, L"Consolas");
    if (c->font) SendDlgItemMessageW(dlg, AB_LOG, WM_SETFONT, (WPARAM)c->font, TRUE);
    {
        HFONT base = (HFONT)SendMessageW(dlg, WM_GETFONT, 0, 0);
        LOGFONTW lf;
        if (base && GetObjectW(base, sizeof(lf), &lf)) {
            lf.lfUnderline = TRUE;
            c->linkFont = CreateFontIndirectW(&lf);
            if (c->linkFont) SendDlgItemMessageW(dlg, AB_LINK, WM_SETFONT, (WPARAM)c->linkFont, TRUE);
        }
    }
    SetTimer(dlg, 1, 1000, NULL);   // 診斷記錄每秒更新一次 (只在「關於」頁)
    SelectPage(dlg, c, c->page);
    SetFocus(GetDlgItem(dlg, SD_NAV));
}

static INT_PTR CALLBACK SettingsDlgProc(HWND dlg, UINT msg, WPARAM wp, LPARAM lp) {
    SetCtx* c = (SetCtx*)GetWindowLongPtrW(dlg, GWLP_USERDATA);
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
    case WM_INITDIALOG:
        c = (SetCtx*)lp;
        SetWindowLongPtrW(dlg, GWLP_USERDATA, (LONG_PTR)c);
        g_setDlg = dlg;
        g_monDlgHwnd = dlg;
        SetupSettingsDlg(dlg, c);
        return FALSE;   // 焦點已自行設定
    case WM_SD_SELPAGE:
        if (c) SelectPage(dlg, c, (int)wp);
        return TRUE;
    case WM_SD_IMGCHANGED:
        if (c) {
            if ((int)wp < 0) ImgPageLoad(dlg, c);
            else if ((int)wp == c->imgSel) ImgPageLoadGeom(dlg, c);
        }
        return TRUE;
    case WM_MEASUREITEM: {   // 左側選單：每一項的高度
        MEASUREITEMSTRUCT* mi = (MEASUREITEMSTRUCT*)lp;
        if (mi->CtlID != SD_NAV) break;
        mi->itemHeight = (UINT)MulDiv(24, OverlayDpi(), 96);
        return TRUE;
    }
    case WM_DRAWITEM: {   // 左側選單：選取項目用反白色，文字垂直置中
        const DRAWITEMSTRUCT* di = (const DRAWITEMSTRUCT*)lp;
        if (di->CtlID != SD_NAV) break;
        if ((int)di->itemID < 0) return TRUE;
        bool sel = (di->itemState & ODS_SELECTED) != 0;
        FillRect(di->hDC, &di->rcItem, GetSysColorBrush(sel ? COLOR_HIGHLIGHT : COLOR_WINDOW));
        wchar_t txt[128] = L"";
        SendMessageW(di->hwndItem, LB_GETTEXT, (WPARAM)di->itemID, (LPARAM)txt);
        HFONT f = (HFONT)SendMessageW(di->hwndItem, WM_GETFONT, 0, 0);
        HGDIOBJ old = f ? SelectObject(di->hDC, f) : NULL;
        SetBkMode(di->hDC, TRANSPARENT);
        SetTextColor(di->hDC, GetSysColor(sel ? COLOR_HIGHLIGHTTEXT : COLOR_WINDOWTEXT));
        RECT tr = di->rcItem;
        tr.left += MulDiv(8, OverlayDpi(), 96);
        tr.right -= MulDiv(4, OverlayDpi(), 96);
        DrawTextW(di->hDC, txt, -1, &tr, DT_SINGLELINE | DT_VCENTER | DT_LEFT | DT_NOPREFIX | DT_END_ELLIPSIS);
        if (old) SelectObject(di->hDC, old);
        if ((di->itemState & ODS_FOCUS) && !(di->itemState & ODS_NOFOCUSRECT)) DrawFocusRect(di->hDC, &di->rcItem);
        return TRUE;
    }
    case WM_TIMER:
        if (c && c->page == SP_ABOUT) UpdateAboutLog(dlg, c);
        return TRUE;
    case WM_CTLCOLORSTATIC: {
        int id = GetDlgCtrlID((HWND)lp);
        if (c && id == SD_I_COLORSW && c->imgSw) return (INT_PTR)c->imgSw;
        if (c && id == MD_TEXTSWATCH && c->sw[0]) return (INT_PTR)c->sw[0];
        if (c && id == MD_OUTSWATCH && c->sw[1]) return (INT_PTR)c->sw[1];
        if (c && id == MD_BGSWATCH && c->sw[2]) return (INT_PTR)c->sw[2];
        if (id == AB_LINK) {   // 連結：藍色文字
            HDC dc = (HDC)wp;
            SetTextColor(dc, RGB(0, 102, 204));
            SetBkColor(dc, GetSysColor(COLOR_BTNFACE));
            return (INT_PTR)GetSysColorBrush(COLOR_BTNFACE);
        }
        break;
    }
    case WM_SETCURSOR:   // 連結：滑鼠變成手形
        if ((HWND)wp == GetDlgItem(dlg, AB_LINK) && IsWindowVisible((HWND)wp)) {
            SetCursor(LoadCursorW(NULL, MAKEINTRESOURCEW(32649)));   // IDC_HAND
            SetWindowLongPtrW(dlg, DWLP_MSGRESULT, TRUE);
            return TRUE;
        }
        break;
    case WM_COMMAND: {
        int id = LOWORD(wp);
        int code = HIWORD(wp);
        if (c && ImgPageCommand(dlg, c, id, code)) return TRUE;   // 圖片置頂頁
        if (id == SD_NAV && code == LBN_SELCHANGE) {
            int sel = (int)SendDlgItemMessageW(dlg, SD_NAV, LB_GETCURSEL, 0, 0);
            if (c && sel >= 0 && sel != c->page) SelectPage(dlg, c, sel);
            return TRUE;
        }
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
        if (id == SD_W_RESET && code == BN_CLICKED) {   // 重置視窗大小和位置：立即執行 (和選單相同)
            HandleCommand(ID_RESET);
            if (c) {
                c->base.borderless = g_borderless;
                DlgSetChecked(dlg, SD_W_BORDERLESS, g_borderless);
            }
            return TRUE;
        }
        if ((id == SD_P_ALL || id == SD_P_P || id == SD_P_PNOHT || id == SD_P_E) && code == BN_CLICKED) {
            unsigned long long m = (unsigned long long)g_maskAll;
            if (id == SD_P_P) m = (unsigned long long)g_maskP;
            else if (id == SD_P_PNOHT) m = (unsigned long long)g_maskPnoHT;
            else if (id == SD_P_E) m = (unsigned long long)g_maskE;
            AffListSet(GetDlgItem(dlg, SD_P_AFF), m);
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
        if (id == AB_LINK && code == 0) {   // STN_CLICKED
            OpenUrl(APP_URL_WSTR);
            return TRUE;
        }
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
        if (id == MD_APPLY && c) {
            ImgPageApplyEdits(dlg, c);
            bool lc = false;
            if (CommitSettings(dlg, c, false, &lc) && lc) {   // 變更語言後重新建立視窗，套用新語言
                c->reopen = true;
                EndDialog(dlg, IDRETRY);
            }
            return TRUE;
        }
        if (id == IDOK && c) {
            ImgPageApplyEdits(dlg, c);
            bool lc = false;
            if (!CommitSettings(dlg, c, true, &lc)) return TRUE;
            EndDialog(dlg, IDOK);
            return TRUE;
        }
        if (id == IDCANCEL) {
            if (c) ApplyOvSettings(c->before);   // 監控設定回復到開啟視窗之前的狀態
            EndDialog(dlg, IDCANCEL);
            return TRUE;
        }
        break;
    }
    case WM_DESTROY:
        KillTimer(dlg, 1);
        if (c) {
            for (int i = 0; i < 3; ++i) {
                if (c->sw[i]) DeleteObject(c->sw[i]);
                c->sw[i] = NULL;
            }
            if (c->imgSw) DeleteObject(c->imgSw);
            c->imgSw = NULL;
            if (c->font) {
                DeleteObject(c->font);
                c->font = NULL;
            }
            if (c->linkFont) {
                DeleteObject(c->linkFont);
                c->linkFont = NULL;
            }
        }
        g_monDlgHwnd = NULL;
        g_setDlg = NULL;
        g_monPreview = false;
        g_ovDebug = false;
        break;
    }
    return FALSE;
}

static void BuildSettingsTemplate(std::vector<WORD>& t, SetCtx* c) {
    const WORD BTN = 0x0080, EDT = 0x0081, STC = 0x0082, LST = 0x0083, CMB = 0x0085, NOID = 0xFFFF;
    DWORD style = DS_MODALFRAME | DS_SETFONT | DS_CENTER | DS_SETFOREGROUND | WS_POPUP | WS_CAPTION | WS_SYSMENU;
    t.push_back((WORD)(style & 0xFFFF));
    t.push_back((WORD)(style >> 16));
    t.push_back(0);
    t.push_back(0);                 // 擴充樣式
    size_t cditPos = t.size();
    t.push_back(0);                 // 控制項數量 (稍後填入)
    t.push_back(0);
    t.push_back(0);                 // x, y
    t.push_back(416);
    t.push_back(396);               // cx, cy (對話框單位)
    t.push_back(0);                 // 選單
    t.push_back(0);                 // 類別
    TmplStr(t, T(S_SET_TITLE));
    t.push_back(9);                 // 字型大小
    TmplStr(t, L"Segoe UI");

    int n = 0;
    WORD autoId = SD_AUTO_BASE;
    // 一般控制項：page = 所屬頁面 (-1 = 每頁都顯示)；頁面內容的 x 座標以 8 ~ 322 計算，這裡再往右移 (留出左側選單的位置)
    auto raw = [&](int page, DWORD st, int x, int y, int cx, int cy, WORD id, WORD cls, const wchar_t* text) {
        if (id == NOID) id = autoId++;
        TmplItem(t, WS_CHILD | WS_VISIBLE | st, (short)x, (short)y, (short)cx, (short)cy, id, cls, text);
        ++n;
        c->pageOf.push_back(std::make_pair(id, page));
    };
    const int OX = 86;
    auto pg = [&](int page, DWORD st, int x, int y, int cx, int cy, WORD id, WORD cls, const wchar_t* text) {
        raw(page, st, x + OX, y, cx, cy, id, cls, text);
    };
    const DWORD CHK = BS_AUTOCHECKBOX | WS_TABSTOP;
    const DWORD COMBO = WS_TABSTOP | WS_VSCROLL | CBS_DROPDOWNLIST;
    const DWORD HEXEDIT = WS_TABSTOP | WS_BORDER | ES_AUTOHSCROLL | ES_UPPERCASE;
    const DWORD HEXEDIT_PLAIN = WS_TABSTOP | WS_BORDER | ES_AUTOHSCROLL;
    const DWORD LISTBOX = LBS_NOTIFY | LBS_NOINTEGRALHEIGHT | WS_BORDER | WS_TABSTOP;

    // 左側選單
    raw(-1, LBS_NOTIFY | LBS_NOINTEGRALHEIGHT | LBS_OWNERDRAWFIXED | LBS_HASSTRINGS | WS_BORDER | WS_TABSTOP, 8, 8, 78, 358, SD_NAV, LST, L"");   // 自行繪製：文字垂直置中

    // ---- 遊戲視窗 ----
    auto win = [&](DWORD st, int x, int y, int cx, int cy, WORD id, WORD cls, const wchar_t* text) { pg(SP_WINDOW, st, x, y, cx, cy, id, cls, text); };
    win(BS_GROUPBOX, 8, 6, 314, 134, NOID, BTN, T(S_G_WINDOW));
    win(CHK, 16, 20, 298, 12, SD_W_BORDERLESS, BTN, T(S_BORDERLESS));
    win(CHK, 16, 36, 298, 12, SD_W_LOCK, BTN, T(S_M_LOCK));
    win(SS_LEFT, 30, 54, 70, 10, NOID, STC, T(S_LOCKSTYLE));
    win(COMBO, 102, 52, 210, 80, SD_W_LOCKSTYLE, CMB, L"");
    win(CHK, 16, 72, 298, 12, SD_W_HIDETB, BTN, T(S_M_HIDE_TASKBAR));
    win(BS_PUSHBUTTON | WS_TABSTOP, 16, 90, 170, 14, SD_W_RESET, BTN, T(S_M_RESET));
    win(SS_LEFT, 16, 110, 298, 26, NOID, STC, T(S_NOTE_WINDOWED));
    win(BS_GROUPBOX, 8, 146, 314, 92, NOID, BTN, T(S_G_MOUSE));
    win(CHK, 16, 160, 298, 12, SD_W_CLIP, BTN, T(S_M_MOUSE_CLIP));
    win(SS_LEFT, 30, 178, 100, 10, NOID, STC, T(S_CLIP_MARGIN));
    win(HEXEDIT_PLAIN | ES_NUMBER, 134, 176, 36, 12, SD_W_MARGIN, EDT, L"");
    win(SS_LEFT, 176, 178, 60, 10, NOID, STC, T(S_CLIP_RANGE));
    win(CHK, 30, 194, 284, 12, SD_W_CLIPBL, BTN, T(S_CLIP_BL));
    win(SS_LEFT, 16, 214, 298, 20, NOID, STC, T(S_TIP_FULLSCREEN));

    // ---- 優先權 / 親和性 ----
    auto pri = [&](DWORD st, int x, int y, int cx, int cy, WORD id, WORD cls, const wchar_t* text) { pg(SP_PRIO, st, x, y, cx, cy, id, cls, text); };
    pri(BS_GROUPBOX, 8, 6, 314, 70, NOID, BTN, T(S_G_PRIO));
    pri(SS_LEFT, 16, 22, 96, 10, NOID, STC, T(S_M_CPUPRIO));
    pri(COMBO, 116, 20, 196, 100, SD_P_CPU, CMB, L"");
    pri(SS_LEFT, 16, 40, 96, 10, NOID, STC, T(S_M_GPUPRIO));
    pri(COMBO, 116, 38, 196, 100, SD_P_GPU, CMB, L"");
    pri(SS_LEFT, 16, 58, 96, 10, NOID, STC, T(S_M_IOPRIO));
    pri(COMBO, 116, 56, 196, 100, SD_P_IO, CMB, L"");
    pri(BS_GROUPBOX, 8, 80, 314, 238, NOID, BTN, T(S_M_CPUAFF));
    pri(BS_PUSHBUTTON | WS_TABSTOP, 16, 94, 150, 14, SD_P_ALL, BTN, T(S_AFF_ALL));
    if (g_hybrid) {
        pri(BS_PUSHBUTTON | WS_TABSTOP, 170, 94, 150, 14, SD_P_P, BTN, T(S_AFF_P));
        pri(BS_PUSHBUTTON | WS_TABSTOP, 16, 110, 150, 14, SD_P_PNOHT, BTN, TS(S_AFF_PNOHT).c_str());
        pri(BS_PUSHBUTTON | WS_TABSTOP, 170, 110, 150, 14, SD_P_E, BTN, T(S_AFF_E));
    } else if (g_maskPnoHT != g_maskAll) {
        pri(BS_PUSHBUTTON | WS_TABSTOP, 170, 94, 150, 14, SD_P_PNOHT, BTN, TS(S_AFF_NOHT).c_str());   // 有超執行緒 / SMT 的一般 CPU
    }
    {
        TmplItemCls(t, WS_CHILD | WS_VISIBLE | WS_BORDER | WS_TABSTOP | LVS_REPORT | LVS_NOCOLUMNHEADER | LVS_SINGLESEL | LVS_SHOWSELALWAYS,
                    (short)(16 + OX), 128, 298, 184, SD_P_AFF, L"SysListView32", L"");
        ++n;
        c->pageOf.push_back(std::make_pair((WORD)SD_P_AFF, (int)SP_PRIO));
    }
    pri(CHK, 8, 324, 314, 12, SD_P_TIP, BTN, T(S_M_TIPSHOW));

    // ---- CPU 限制 ----
    auto cpu = [&](DWORD st, int x, int y, int cx, int cy, WORD id, WORD cls, const wchar_t* text) { pg(SP_CPU, st, x, y, cx, cy, id, cls, text); };
    cpu(BS_GROUPBOX, 8, 6, 314, 96, NOID, BTN, T(S_M_LIMIT));
    cpu(CHK, 16, 20, 298, 12, SD_C_ENABLE, BTN, T(S_M_ENABLE));
    cpu(CHK, 16, 36, 298, 12, SD_C_ECO, BTN, T(S_M_ECO));
    cpu(SS_LEFT, 16, 58, 96, 10, NOID, STC, T(S_M_COND));
    cpu(COMBO, 116, 56, 196, 80, SD_C_COND, CMB, L"");
    cpu(SS_LEFT, 16, 76, 96, 10, NOID, STC, T(S_M_RATIO));
    cpu(COMBO, 116, 74, 90, 100, SD_C_RATIO, CMB, L"");

    // ---- 效能監控 ----
    auto mon = [&](DWORD st, int x, int y, int cx, int cy, WORD id, WORD cls, const wchar_t* text) { pg(SP_MON, st, x, y, cx, cy, id, cls, text); };
    // 啟用監控 (最上方)
    mon(CHK, 8, 6, 250, 12, MD_ENABLE, BTN, T(S_MON_ENABLE));

    // 顯示項目 (左) 與顯示順序 (右，用滑鼠拖曳調整)
    mon(BS_GROUPBOX, 8, 22, 212, 106, NOID, BTN, T(S_MON_ITEMS));
    mon(CHK, 14, 36, 38, 12, MD_CPU, BTN, L"CPU");
    mon(CHK, 54, 36, 44, 12, MD_CPU_PCT, BTN, T(S_MON_PCT));
    mon(CHK, 100, 36, 116, 12, MD_CPU_ACT, BTN, T(S_MON_ACTUAL_GHZ));
    mon(CHK, 14, 50, 38, 12, MD_RAM, BTN, L"RAM");
    mon(CHK, 54, 50, 44, 12, MD_RAM_PCT, BTN, T(S_MON_PCT));
    mon(CHK, 100, 50, 116, 12, MD_RAM_ACT, BTN, T(S_MON_ACTUAL_MB));
    mon(CHK, 14, 64, 100, 12, MD_GPU, BTN, L"GPU");
    mon(CHK, 14, 78, 38, 12, MD_VRAM, BTN, L"VRAM");
    mon(CHK, 54, 78, 44, 12, MD_VRAM_PCT, BTN, T(S_MON_PCT));
    mon(CHK, 100, 78, 116, 12, MD_VRAM_ACT, BTN, T(S_MON_ACTUAL_MB));
    mon(CHK, 14, 92, 100, 12, MD_FPS, BTN, L"FPS");
    mon(CHK, 14, 106, 100, 12, MD_LAT, BTN, L"Latency");
    mon(BS_GROUPBOX, 224, 22, 98, 106, NOID, BTN, T(S_MON_ORDER));
    mon(LISTBOX, 230, 36, 86, 86, MD_ORDER, LST, L"");

    // 顯示設定：排列方式 (橫式可設定分隔文字)、更新頻率、CPU 使用率算法
    mon(BS_GROUPBOX, 8, 130, 314, 84, NOID, BTN, T(S_MON_DISPLAY));
    mon(SS_LEFT, 16, 144, 68, 10, NOID, STC, T(S_MON_LAYOUT));
    mon(COMBO, 88, 142, 100, 80, MD_LAYOUT, CMB, L"");
    mon(SS_LEFT, 194, 144, 44, 10, NOID, STC, T(S_MON_SEPARATOR));
    mon(HEXEDIT_PLAIN, 240, 142, 72, 12, MD_SEP, EDT, L"");
    mon(SS_LEFT, 16, 162, 68, 10, NOID, STC, T(S_MON_INTERVAL));
    mon(COMBO, 88, 160, 224, 80, MD_INTERVAL, CMB, L"");
    mon(SS_LEFT, 16, 180, 68, 10, NOID, STC, T(S_MON_METHOD));
    mon(COMBO, 88, 178, 224, 80, MD_METHOD, CMB, L"");
    mon(SS_LEFT, 16, 198, 68, 10, NOID, STC, T(S_MON_LATMETHOD));
    mon(COMBO, 88, 196, 224, 80, MD_LATMETHOD, CMB, L"");

    // 外觀
    mon(BS_GROUPBOX, 8, 218, 314, 114, NOID, BTN, T(S_MON_STYLE));
    mon(SS_LEFT, 16, 234, 90, 10, NOID, STC, T(S_MON_FONTSIZE));
    mon(COMBO, 110, 232, 90, 80, MD_FONT, CMB, L"");
    mon(SS_LEFT, 16, 250, 90, 10, NOID, STC, T(S_LBL_TEXTCOLOR));
    mon(HEXEDIT, 110, 248, 52, 12, MD_TEXTCOLOR, EDT, L"");
    mon(WS_BORDER | SS_LEFT, 168, 248, 14, 12, MD_TEXTSWATCH, STC, L"");
    mon(SS_LEFT, 16, 266, 90, 10, NOID, STC, T(S_LBL_OUTLINECOLOR));
    mon(HEXEDIT, 110, 264, 52, 12, MD_OUTLINE, EDT, L"");
    mon(WS_BORDER | SS_LEFT, 168, 264, 14, 12, MD_OUTSWATCH, STC, L"");
    mon(SS_LEFT, 16, 282, 90, 10, NOID, STC, T(S_MON_OPACITY));
    mon(COMBO, 110, 280, 90, 80, MD_OPACITY, CMB, L"");
    mon(SS_LEFT, 16, 298, 90, 10, NOID, STC, T(S_LBL_BGCOLOR));
    mon(HEXEDIT, 110, 296, 52, 12, MD_BGCOLOR, EDT, L"");
    mon(WS_BORDER | SS_LEFT, 168, 296, 14, 12, MD_BGSWATCH, STC, L"");
    mon(CHK, 16, 312, 290, 12, MD_LOCKNOBG, BTN, T(S_MON_LOCKNOBG));

    // 其他
    mon(CHK, 8, 338, 314, 12, MD_FGONLY, BTN, T(S_MON_FGONLY_DLG));
    mon(CHK, 8, 354, 220, 12, MD_LOCK, BTN, T(S_MON_LOCK));
    mon(BS_PUSHBUTTON | WS_TABSTOP, 236, 352, 86, 14, MD_RESETPOS, BTN, T(S_MON_RESETPOS));

    // ---- 圖片置頂 ----
    auto img = [&](DWORD st, int x, int y, int cx, int cy, WORD id, WORD cls, const wchar_t* text) { pg(SP_IMG, st, x, y, cx, cy, id, cls, text); };
    const DWORD NUMEDIT = HEXEDIT_PLAIN | ES_NUMBER;
    img(CHK, 8, 6, 314, 12, SD_I_MASTER, BTN, T(S_IMG_MASTER));
    img(CHK, 8, 20, 314, 12, SD_I_LOCKALL, BTN, T(S_IMG_LOCKALL));
    img(BS_GROUPBOX, 8, 36, 314, 262, NOID, BTN, T(S_IMG_GROUPBOX));
    img(SS_LEFT, 16, 52, 60, 10, NOID, STC, T(S_IMG_SEL));
    img(COMBO, 80, 50, 232, 120, SD_I_SEL, CMB, L"");
    img(CHK, 16, 68, 90, 12, SD_I_ENABLE, BTN, T(S_IMG_ENABLE));
    img(CHK, 110, 68, 130, 12, SD_I_LOCK, BTN, T(S_IMG_LOCK));
    img(SS_LEFT, 16, 86, 60, 10, NOID, STC, T(S_IMG_NAME));
    img(HEXEDIT_PLAIN, 80, 84, 232, 12, SD_I_NAME, EDT, L"");
    img(SS_LEFT, 16, 102, 60, 10, NOID, STC, T(S_IMG_SRC));
    img(COMBO, 80, 100, 150, 80, SD_I_SRC, CMB, L"");
    img(SS_LEFT, 236, 102, 8, 10, NOID, STC, L"#");
    img(HEXEDIT_PLAIN, 246, 100, 46, 12, SD_I_COLOR, EDT, L"");
    img(WS_BORDER | SS_LEFT, 296, 100, 14, 12, SD_I_COLORSW, STC, L"");
    img(SS_LEFT, 16, 118, 60, 10, NOID, STC, T(S_IMG_PATH));
    img(HEXEDIT_PLAIN, 80, 116, 178, 12, SD_I_PATH, EDT, L"");
    img(BS_PUSHBUTTON | WS_TABSTOP, 262, 115, 50, 14, SD_I_BROWSE, BTN, T(S_IMG_BROWSE));
    img(SS_LEFT, 16, 136, 62, 10, NOID, STC, T(S_IMG_OPACITY));
    img(NUMEDIT, 80, 134, 32, 12, SD_I_OPACITY, EDT, L"");
    img(SS_LEFT, 116, 136, 40, 10, NOID, STC, L"(5 ~ 100)");
    img(SS_LEFT, 170, 136, 70, 10, NOID, STC, T(S_IMG_SCALE));
    img(NUMEDIT, 244, 134, 36, 12, SD_I_SCALE, EDT, L"");
    img(SS_LEFT, 16, 156, 10, 10, NOID, STC, L"X");
    img(HEXEDIT_PLAIN, 28, 154, 40, 12, SD_I_X, EDT, L"");
    img(SS_LEFT, 78, 156, 10, 10, NOID, STC, L"Y");
    img(HEXEDIT_PLAIN, 90, 154, 40, 12, SD_I_Y, EDT, L"");
    img(SS_LEFT, 142, 156, 22, 10, NOID, STC, T(S_IMG_W));
    img(NUMEDIT, 166, 154, 40, 12, SD_I_W, EDT, L"");
    img(SS_LEFT, 216, 156, 22, 10, NOID, STC, T(S_IMG_H));
    img(NUMEDIT, 240, 154, 40, 12, SD_I_H, EDT, L"");
    img(CHK, 16, 174, 100, 12, SD_I_FLIP, BTN, T(S_IMG_FLIP));
    img(SS_LEFT, 124, 176, 36, 10, NOID, STC, T(S_IMG_ROT));
    img(COMBO, 162, 172, 56, 80, SD_I_ROT, CMB, L"");
    img(SS_LEFT, 16, 196, 150, 10, NOID, STC, T(S_IMG_Z));
    img(COMBO, 170, 194, 50, 120, SD_I_Z, CMB, L"");
    img(CHK, 16, 212, 296, 12, SD_I_FGONLY, BTN, T(S_IMG_FGONLY));
    img(CHK, 16, 228, 130, 12, SD_I_GIFPAUSE, BTN, T(S_IMG_GIFPAUSE));
    img(SS_LEFT, 150, 230, 62, 10, NOID, STC, T(S_IMG_GIFSPEED));
    img(COMBO, 214, 226, 98, 100, SD_I_GIFSPEED, CMB, L"");
    img(BS_PUSHBUTTON | WS_TABSTOP, 16, 246, 130, 14, SD_I_RESETSIZE, BTN, T(S_IMG_RESETSIZE));
    img(SS_LEFT, 16, 266, 296, 30, NOID, STC, T(S_IMG_NOTE));

    // ---- 其他 ----
    auto oth = [&](DWORD st, int x, int y, int cx, int cy, WORD id, WORD cls, const wchar_t* text) { pg(SP_OTHER, st, x, y, cx, cy, id, cls, text); };
    oth(SS_LEFT, 8, 12, 120, 10, NOID, STC, T(S_M_DBLCLICK));
    oth(COMBO, 132, 10, 190, 100, SD_O_DBL, CMB, L"");
    oth(SS_LEFT, 8, 32, 120, 10, NOID, STC, T(S_M_LANG));
    oth(COMBO, 132, 30, 190, 100, SD_O_LANG, CMB, L"");

    // ---- 關於 ----
    auto abt = [&](DWORD st, int x, int y, int cx, int cy, WORD id, WORD cls, const wchar_t* text) { pg(SP_ABOUT, st, x, y, cx, cy, id, cls, text); };
    std::wstring verText = L"Mabinogi Client Manager  v" APP_VERSION_WSTR;
    const DWORD LOGEDIT = ES_MULTILINE | ES_READONLY | ES_AUTOVSCROLL | ES_AUTOHSCROLL | WS_VSCROLL | WS_HSCROLL | WS_BORDER | WS_TABSTOP;
    abt(BS_GROUPBOX, 8, 6, 314, 120, NOID, BTN, T(S_ABOUT_GROUP));
    abt(SS_LEFT, 14, 18, 302, 10, NOID, STC, verText.c_str());
    abt(SS_LEFT | SS_NOTIFY, 14, 29, 175, 10, AB_LINK, STC, APP_URL_WSTR);   // 版本號下一行：GitHub 連結 (點了開啟網址)
    abt(SS_LEFT, 14, 44, 302, 78, NOID, STC, T(S_ABOUT_TEXT));
    abt(BS_GROUPBOX, 8, 130, 314, 226, NOID, BTN, T(S_MON_DEBUG));
    abt(LOGEDIT, 14, 142, 302, 190, AB_LOG, EDT, L"");
    abt(BS_PUSHBUTTON | WS_TABSTOP, 14, 336, 50, 14, AB_COPY, BTN, T(S_DLG_COPY));
    abt(BS_PUSHBUTTON | WS_TABSTOP, 68, 336, 64, 14, AB_PAUSE, BTN, T(S_DLG_STOP_UPDATE));

    // ---- 確定 / 取消 / 套用 (每頁都顯示) ----
    raw(-1, BS_DEFPUSHBUTTON | WS_TABSTOP, 256, 374, 48, 14, IDOK, BTN, T(S_DLG_OK));
    raw(-1, BS_PUSHBUTTON | WS_TABSTOP, 308, 374, 48, 14, IDCANCEL, BTN, T(S_DLG_CANCEL));
    raw(-1, BS_PUSHBUTTON | WS_TABSTOP, 360, 374, 48, 14, MD_APPLY, BTN, T(S_DLG_APPLY));
    t[cditPos] = (WORD)n;
}

static void ShowSettingsDialog(int page = -1) {
    if (g_setDlg) {
        if (page >= 0) PostMessageW(g_setDlg, WM_SD_SELPAGE, (WPARAM)page, 0);
        SetForegroundWindow(g_setDlg);
        return;
    }
    SetCtx ctx;
    ctx.before = CaptureOv();   // 開啟視窗時的監控設定 (按取消時回復)
    ctx.sw[0] = ctx.sw[1] = ctx.sw[2] = NULL;
    ctx.imgSw = NULL;
    ctx.dragIdx = -1;
    ctx.insertPos = -1;
    ctx.page = (page >= 0 && page < SP_COUNT) ? page : SP_WINDOW;
    ctx.imgSel = 0;
    ctx.font = NULL;
    ctx.linkFont = NULL;
    ctx.paused = false;
    ctx.reopen = false;
    if (!g_dragListMsg) g_dragListMsg = RegisterWindowMessageW(L"commctrl_DragListMsg");
    g_monDlgOpen = true;
    for (;;) {
        ctx.monBase = CaptureOv();
        ctx.base = CaptureSetVals();
        ctx.lastLog.clear();
        ctx.reopen = false;
        ctx.pageOf.clear();
        ctx.insertPos = -1;
        std::vector<WORD> t;
        BuildSettingsTemplate(t, &ctx);
        INT_PTR r = DialogBoxIndirectParamW(g_hInst, (LPCDLGTEMPLATEW)t.data(), g_hWnd, SettingsDlgProc, (LPARAM)&ctx);
        if (!(r == IDRETRY && ctx.reopen)) break;
    }
    g_monDlgOpen = false;
    g_monPreview = false;
    g_ovDebug = false;
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
    AppendMenuW(parent, MF_POPUP, (UINT_PTR)mon, T(S_M_MON));
}

static void BuildImageMenu(HMENU parent) {
    HMENU m = CreatePopupMenu();
    AppendMenuW(m, MF_STRING | Chk(g_imgMaster), ID_IMG_MASTER, T(S_IMG_MASTER));
    AppendMenuW(m, MF_STRING | Chk(g_imgLockAll), ID_IMG_LOCKALL, T(S_IMG_LOCKALL));
    AppendMenuW(m, MF_SEPARATOR, 0, NULL);
    for (int i = 0; i < kImgGroups; ++i) {
        wchar_t b[64];
        wsprintfW(b, T(S_IMG_GROUP), i + 1);
        std::wstring s = b;
        if (!g_img[i].name.empty()) {
            std::wstring nm = g_img[i].name;
            for (size_t k = nm.find(L'&'); k != std::wstring::npos; k = nm.find(L'&', k + 2)) nm.insert(k, 1, L'&');   // 選單的 & 是快速鍵符號
            s += L"：";
            s += nm;
        }
        AppendMenuW(m, MF_STRING | Chk(g_img[i].enabled), ID_IMG_GROUP_BASE + i, s.c_str());
    }
    AppendMenuW(m, MF_SEPARATOR, 0, NULL);
    AppendMenuW(m, MF_STRING, ID_IMG_SETTINGS, T(S_IMG_SETTINGS));
    AppendMenuW(parent, MF_POPUP, (UINT_PTR)m, T(S_M_IMG));
}

static void HandleImageCommand(int id) {
    if (id == ID_IMG_SETTINGS) {
        ShowSettingsDialog(SP_IMG);
        return;
    }
    if (id == ID_IMG_MASTER) {
        g_imgMaster = !g_imgMaster;
        SaveInt(L"ImgMaster", g_imgMaster ? 1 : 0);
        ImgSyncAll();
    } else if (id == ID_IMG_LOCKALL) {
        g_imgLockAll = !g_imgLockAll;
        SaveInt(L"ImgLockAll", g_imgLockAll ? 1 : 0);
        ImgSyncAll();
    } else if (id >= ID_IMG_GROUP_BASE && id < ID_IMG_GROUP_BASE + kImgGroups) {
        int i = id - ID_IMG_GROUP_BASE;
        g_img[i].enabled = !g_img[i].enabled;
        SaveIntS(ImgSec(i), L"Enabled", g_img[i].enabled ? 1 : 0);
        ImgSync(i, true);
    }
    ImgNotifyDlg(-1);   // 設定視窗開啟時同步更新畫面上的勾選
}

static void HandleOverlayCommand(int id) {
    if (g_monDlgOpen) {   // 設定視窗開啟期間，監控選項請在設定視窗內調整
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

// ---------------------------------------------------------------------------
//  圖示上方的短暫提示：連點兩下圖示切換功能後，在通知區域圖示附近顯示「項目：已啟用 / 已關閉」，約 1.8 秒後自動消失
//  (使用標準的 tooltips_class32 追蹤式提示框，不使用系統的「通知」，所以不會被專注輔助或通知設定擋掉)
// ---------------------------------------------------------------------------
static HWND g_toastTip = NULL;
static bool g_toastShown = false;
static std::wstring g_toastText;

static void HideToast() {
    if (g_hWnd) KillTimer(g_hWnd, 8);
    if (!g_toastTip || !g_toastShown) return;
    TTTOOLINFOW ti;
    ZeroMemory(&ti, sizeof(ti));
    ti.cbSize = TTTOOLINFOW_V1_SIZE;
    ti.hwnd = g_hWnd;
    ti.uId = 2;
    SendMessageW(g_toastTip, TTM_TRACKACTIVATE, FALSE, (LPARAM)&ti);
    g_toastShown = false;
}

static void ShowToast(const std::wstring& text) {
    if (!g_toastTip) {
        g_toastTip = CreateWindowExW(WS_EX_TOPMOST, TOOLTIPS_CLASSW, NULL, WS_POPUP | TTS_NOPREFIX | TTS_ALWAYSTIP,
                                     CW_USEDEFAULT, CW_USEDEFAULT, CW_USEDEFAULT, CW_USEDEFAULT, g_hWnd, NULL, g_hInst, NULL);
        if (!g_toastTip) return;
        TTTOOLINFOW ti0;
        ZeroMemory(&ti0, sizeof(ti0));
        ti0.cbSize = TTTOOLINFOW_V1_SIZE;
        ti0.uFlags = TTF_TRACK | TTF_ABSOLUTE;   // 追蹤式提示框：位置由我們指定
        ti0.hwnd = g_hWnd;
        ti0.uId = 2;
        ti0.lpszText = (LPWSTR)L"";
        SendMessageW(g_toastTip, TTM_ADDTOOLW, 0, (LPARAM)&ti0);
        SendMessageW(g_toastTip, TTM_SETMAXTIPWIDTH, 0, MulDiv(400, OverlayDpi(), 96));
    }
    g_toastText = text;
    TTTOOLINFOW ti;
    ZeroMemory(&ti, sizeof(ti));
    ti.cbSize = TTTOOLINFOW_V1_SIZE;
    ti.hwnd = g_hWnd;
    ti.uId = 2;
    ti.lpszText = (LPWSTR)g_toastText.c_str();
    SendMessageW(g_toastTip, TTM_UPDATETIPTEXTW, 0, (LPARAM)&ti);

    // 錨點：通知區域圖示 (取不到時用滑鼠位置：連點兩下的當下滑鼠就在圖示上)
    int dpi = OverlayDpi();
    RECT ic;
    NOTIFYICONIDENTIFIER nii;
    ZeroMemory(&nii, sizeof(nii));
    nii.cbSize = sizeof(nii);
    nii.hWnd = g_hWnd;
    nii.uID = 1;
    if (!SUCCEEDED(Shell_NotifyIconGetRect(&nii, &ic))) {
        POINT p;
        GetCursorPos(&p);
        ic.left = ic.right = p.x;
        ic.top = ic.bottom = p.y;
    }
    // 提示框大小
    // (舊版 comctl32 v5.82 不支援 TTM_GETBUBBLESIZE，用字型量測文字寬度來估計，做法同選單提示)
    HFONT f = (HFONT)SendMessageW(g_toastTip, WM_GETFONT, 0, 0);
    HDC dc = GetDC(NULL);
    HGDIOBJ oldf = f ? SelectObject(dc, f) : NULL;
    SIZE sz = { 0, 0 };
    GetTextExtentPoint32W(dc, g_toastText.c_str(), (int)g_toastText.size(), &sz);
    if (oldf) SelectObject(dc, oldf);
    ReleaseDC(NULL, dc);
    int tw = sz.cx + MulDiv(16, dpi, 96), th = sz.cy + MulDiv(10, dpi, 96);
    // 工作列在哪一邊，就把提示框放在圖示的內側 (工作列在下方 = 顯示在圖示上方)
    MONITORINFO mi;
    ZeroMemory(&mi, sizeof(mi));
    mi.cbSize = sizeof(mi);
    GetMonitorInfoW(MonitorFromRect(&ic, MONITOR_DEFAULTTONEAREST), &mi);
    int dl = (int)(ic.left - mi.rcMonitor.left), dr = (int)(mi.rcMonitor.right - ic.right);
    int dt = (int)(ic.top - mi.rcMonitor.top), db = (int)(mi.rcMonitor.bottom - ic.bottom);
    int mn = std::min(std::min(dl, dr), std::min(dt, db));
    int gap = MulDiv(6, dpi, 96);
    int cx = (int)((ic.left + ic.right) / 2), cy = (int)((ic.top + ic.bottom) / 2);
    int x, y;
    if (mn == db) {
        x = cx - tw / 2;
        y = (int)ic.top - th - gap;
    } else if (mn == dt) {
        x = cx - tw / 2;
        y = (int)ic.bottom + gap;
    } else if (mn == dl) {
        x = (int)ic.right + gap;
        y = cy - th / 2;
    } else {
        x = (int)ic.left - tw - gap;
        y = cy - th / 2;
    }
    int margin = MulDiv(4, dpi, 96);
    if (x + tw > mi.rcMonitor.right - margin) x = (int)mi.rcMonitor.right - margin - tw;
    if (x < mi.rcMonitor.left + margin) x = (int)mi.rcMonitor.left + margin;
    if (y + th > mi.rcMonitor.bottom - margin) y = (int)mi.rcMonitor.bottom - margin - th;
    if (y < mi.rcMonitor.top + margin) y = (int)mi.rcMonitor.top + margin;
    SendMessageW(g_toastTip, TTM_TRACKPOSITION, 0, MAKELPARAM(x, y));
    SendMessageW(g_toastTip, TTM_TRACKACTIVATE, TRUE, (LPARAM)&ti);
    g_toastShown = true;
    SetTimer(g_hWnd, 8, 1800, NULL);   // 重複設定 = 重新計時
}

// 「項目：已啟用 / 已關閉」
static void ToastState(int nameId, bool on) {
    wchar_t b[256];
    wsprintfW(b, T(on ? S_TOAST_ON : S_TOAST_OFF), T(nameId));
    ShowToast(b);
}

// 連點兩下通知區域圖示：依設定的動作執行。
// 「開啟設定頁面」不需要遊戲；其他動作先確認遊戲是否在執行 (沒有就顯示提示視窗)，
// 切換後在圖示上方短暫顯示該項目目前是啟用還是關閉 (動作沒有生效時不顯示)。
static void OnTrayDoubleClick() {
    int a = g_dblAction;
    if (a == 0) {
        ShowSettingsDialog();
        return;
    }
    if (GetClientPids().empty()) {
        ShowNoGameDialog();
        return;
    }
    if (a == 1) {
        bool before = g_borderless;
        ToggleBorderless();
        if (g_borderless != before) ToastState(S_BORDERLESS, g_borderless);
    } else if (a == 2) {
        g_cpuEnabled = !g_cpuEnabled;
        SaveInt(L"CpuEnabled", g_cpuEnabled ? 1 : 0);
        WakeEngine();
        ToastState(S_M_LIMIT, g_cpuEnabled);
    } else if (a == 3) {
        bool before = g_ovEnabled;
        HandleOverlayCommand(ID_OV_ENABLE);   // 設定視窗開啟時不會切換 (和選單相同)
        if (g_ovEnabled != before) ToastState(S_M_MON, g_ovEnabled);
    } else if (a == 4) {
        bool before = g_hideTaskbar;
        HandleCommand(ID_HIDE_TASKBAR);
        if (g_hideTaskbar != before) ToastState(S_M_HIDE_TASKBAR, g_hideTaskbar);
    }
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

// ---------------------------------------------------------------------------
//  選單提示：滑鼠停在特定選單項目上時 (WM_MENUSELECT)，用標準的 tooltips_class32 在選單旁邊顯示說明
// ---------------------------------------------------------------------------
static HWND g_menuTip = NULL;
static bool g_menuTipShown = false;
static std::wstring g_menuTipText;

static const wchar_t* MenuTipText(UINT id) {
    switch (id) {
    case ID_TOGGLE:
    case ID_LOCK:
    case ID_RESET:
        return T(S_TIP_WINDOWED);
    case ID_MOUSE_CLIP:
        return T(S_TIP_FULLSCREEN);
    }
    return NULL;
}

static void HideMenuTip() {
    if (!g_menuTip || !g_menuTipShown) return;
    TTTOOLINFOW ti;
    ZeroMemory(&ti, sizeof(ti));
    ti.cbSize = TTTOOLINFOW_V1_SIZE;
    ti.hwnd = g_hWnd;
    ti.uId = 1;
    SendMessageW(g_menuTip, TTM_TRACKACTIVATE, FALSE, (LPARAM)&ti);
    g_menuTipShown = false;
}

static void ShowMenuTip(HMENU hm, UINT id, const wchar_t* text) {
    int count = GetMenuItemCount(hm), idx = -1;
    for (int i = 0; i < count; ++i) {
        if (GetMenuItemID(hm, i) == id) {
            idx = i;
            break;
        }
    }
    RECT rc;
    if (idx < 0 || !GetMenuItemRect(NULL, hm, (UINT)idx, &rc)) {
        HideMenuTip();
        return;
    }
    if (!g_menuTip) {
        g_menuTip = CreateWindowExW(WS_EX_TOPMOST, TOOLTIPS_CLASSW, NULL, WS_POPUP | TTS_NOPREFIX | TTS_ALWAYSTIP,
                                    CW_USEDEFAULT, CW_USEDEFAULT, CW_USEDEFAULT, CW_USEDEFAULT, g_hWnd, NULL, g_hInst, NULL);
        if (!g_menuTip) return;
        TTTOOLINFOW ti0;
        ZeroMemory(&ti0, sizeof(ti0));
        ti0.cbSize = TTTOOLINFOW_V1_SIZE;
        ti0.uFlags = TTF_TRACK | TTF_ABSOLUTE;   // 追蹤式提示框：位置由我們指定
        ti0.hwnd = g_hWnd;
        ti0.uId = 1;
        ti0.lpszText = (LPWSTR)L"";
        SendMessageW(g_menuTip, TTM_ADDTOOLW, 0, (LPARAM)&ti0);
        SendMessageW(g_menuTip, TTM_SETMAXTIPWIDTH, 0, MulDiv(400, OverlayDpi(), 96));
    }
    g_menuTipText = text;
    TTTOOLINFOW ti;
    ZeroMemory(&ti, sizeof(ti));
    ti.cbSize = TTTOOLINFOW_V1_SIZE;
    ti.hwnd = g_hWnd;
    ti.uId = 1;
    ti.lpszText = (LPWSTR)g_menuTipText.c_str();
    SendMessageW(g_menuTip, TTM_UPDATETIPTEXTW, 0, (LPARAM)&ti);
    // 估計提示框大小，決定放在選單項目的右側或左側 (選單靠近螢幕右緣時放左側)
    HFONT f = (HFONT)SendMessageW(g_menuTip, WM_GETFONT, 0, 0);
    HDC dc = GetDC(NULL);
    HGDIOBJ oldf = f ? SelectObject(dc, f) : NULL;
    SIZE sz = { 0, 0 };
    GetTextExtentPoint32W(dc, g_menuTipText.c_str(), (int)g_menuTipText.size(), &sz);
    if (oldf) SelectObject(dc, oldf);
    ReleaseDC(NULL, dc);
    int tw = sz.cx + MulDiv(16, OverlayDpi(), 96), th = sz.cy + MulDiv(10, OverlayDpi(), 96);
    MONITORINFO mi;
    ZeroMemory(&mi, sizeof(mi));
    mi.cbSize = sizeof(mi);
    GetMonitorInfoW(MonitorFromRect(&rc, MONITOR_DEFAULTTONEAREST), &mi);
    int gap = MulDiv(4, OverlayDpi(), 96);
    int x = rc.right + gap;
    if (x + tw > mi.rcWork.right) x = rc.left - tw - gap;
    if (x < mi.rcWork.left) x = mi.rcWork.left;
    int y = rc.top + ((rc.bottom - rc.top) - th) / 2;
    if (y + th > mi.rcWork.bottom) y = mi.rcWork.bottom - th;
    if (y < mi.rcWork.top) y = mi.rcWork.top;
    SendMessageW(g_menuTip, TTM_TRACKPOSITION, 0, MAKELPARAM(x, y));
    SendMessageW(g_menuTip, TTM_TRACKACTIVATE, TRUE, (LPARAM)&ti);
    g_menuTipShown = true;
}

static void ShowMenu(HWND hwnd) {
    POINT pt;
    GetCursorPos(&pt);
    int mode = g_mode;
    int ratio = g_ratio;
    HMENU m = CreatePopupMenu();
    // 遊戲正在執行但不是視窗模式 (全螢幕 / 無邊框全視窗)：切換無邊框與重置沒有作用，顯示為灰色 (沒有遊戲時維持可用，按下會顯示「遊戲未啟動」)
    bool inWindowedMode = true;
    {
        std::vector<HWND> gw = GetGameWindows();
        if (!gw.empty()) {
            inWindowedMode = false;
            for (size_t i = 0; i < gw.size(); ++i) {
                if (IsControllable(gw[i], GetState(gw[i]))) inWindowedMode = true;
            }
        }
    }
    UINT grayFlag = inWindowedMode ? 0 : MF_GRAYED;
    AppendMenuW(m, MF_STRING | grayFlag | (g_borderless ? MF_CHECKED : 0), ID_TOGGLE, T(S_M_TOGGLE));
    AppendMenuW(m, MF_STRING | (g_locked ? MF_CHECKED : 0), ID_LOCK, T(S_M_LOCK));
    AppendMenuW(m, MF_STRING | grayFlag, ID_RESET, T(S_M_RESET));
    AppendMenuW(m, MF_SEPARATOR, 0, NULL);
    AppendMenuW(m, MF_STRING | (g_hideTaskbar ? MF_CHECKED : 0), ID_HIDE_TASKBAR, T(S_M_HIDE_TASKBAR));
    AppendMenuW(m, MF_STRING | (g_mouseClip ? MF_CHECKED : 0), ID_MOUSE_CLIP, T(S_M_MOUSE_CLIP));
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
    BuildImageMenu(m);
    AppendMenuW(m, MF_SEPARATOR, 0, NULL);

    HMENU rs = CreatePopupMenu();
    AppendMenuW(rs, MF_STRING, ID_RESTART_CLIENT, T(S_M_RESTART_CLIENT));
    AppendMenuW(rs, MF_STRING, ID_RESTART_LAUNCHER, T(S_M_RESTART_LAUNCHER));
    AppendMenuW(rs, MF_STRING, ID_TERM, T(S_M_TERM));
    AppendMenuW(m, MF_POPUP, (UINT_PTR)rs, T(S_M_RESTARTMENU));
    AppendMenuW(m, MF_SEPARATOR, 0, NULL);

    HMENU dbl = CreatePopupMenu();
    int da = g_dblAction;
    AppendMenuW(dbl, MF_STRING | (da == 0 ? MF_CHECKED : 0), ID_DBL_BASE + 0, T(S_DBL_SETTINGS));
    AppendMenuW(dbl, MF_STRING | (da == 1 ? MF_CHECKED : 0), ID_DBL_BASE + 1, T(S_M_TOGGLE));
    AppendMenuW(dbl, MF_STRING | (da == 2 ? MF_CHECKED : 0), ID_DBL_BASE + 2, T(S_DBL_CPU));
    AppendMenuW(dbl, MF_STRING | (da == 3 ? MF_CHECKED : 0), ID_DBL_BASE + 3, T(S_DBL_MON));
    AppendMenuW(dbl, MF_STRING | (da == 4 ? MF_CHECKED : 0), ID_DBL_BASE + 4, T(S_DBL_TASKBAR));
    AppendMenuW(m, MF_POPUP, (UINT_PTR)dbl, T(S_M_DBLCLICK));

    HMENU lang = CreatePopupMenu();
    int sel = g_langSetting;
    AppendMenuW(lang, MF_STRING | (sel == UL_AUTO ? MF_CHECKED : 0), ID_LANG_BASE + UL_AUTO, T(S_L_AUTO));
    for (int l = UL_ZHTW; l <= UL_KO; ++l) AppendMenuW(lang, MF_STRING | (sel == l ? MF_CHECKED : 0), ID_LANG_BASE + l, LangLabel(l));
    AppendMenuW(m, MF_POPUP, (UINT_PTR)lang, T(S_M_LANG));
    AppendMenuW(m, MF_STRING, ID_SETTINGS, T(S_M_SETTINGS));
    AppendMenuW(m, MF_STRING, ID_EXIT, T(S_M_EXIT));

    SetForegroundWindow(hwnd);
    TrackPopupMenu(m, TPM_BOTTOMALIGN | TPM_LEFTALIGN, pt.x, pt.y, 0, hwnd, NULL);
    HideMenuTip();
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
    case ID_HIDE_TASKBAR:
        if (!g_hideTaskbar && GetClientPids().empty()) {   // 遊戲沒有執行時不能開啟 (關閉則隨時可以)
            ShowNoGameDialog();
            break;
        }
        g_hideTaskbar = !g_hideTaskbar;
        SaveInt(L"HideTaskbar", g_hideTaskbar ? 1 : 0);
        g_tbSig = 0;
        ApplyTaskbarButtons(g_hideTaskbar);
        break;
    case ID_MOUSE_CLIP:
        g_mouseClip = !g_mouseClip;
        if (g_mouseClip) LoadMouseClipMargin();   // 開啟時重新讀取隱藏設定，方便測試時修改 ini
        SaveInt(L"MouseClip", g_mouseClip ? 1 : 0);
        UpdateMouseClip();
        break;
    case ID_SETTINGS:
        ShowSettingsDialog();
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
        } else if (id >= ID_DBL_BASE && id <= ID_DBL_BASE + 4) {
            g_dblAction = id - ID_DBL_BASE;
            SaveInt(L"DoubleClick", g_dblAction);
        } else if (id >= ID_OV_ENABLE && id <= ID_OV_LAST) {
            HandleOverlayCommand(id);
        } else if (id >= ID_IMG_MASTER && id <= ID_IMG_LAST) {
            HandleImageCommand(id);
        } else if (id >= ID_LANG_BASE && id <= ID_LANG_BASE + kLangCount) {
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
        ReleaseTaskbarList();                 // 舊的 COM 物件已失效，下一次偵測時重新建立並再次隱藏
        g_tbLastApply = 0;
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
        } else if (wp == 7) {
            UpdateMouseClip();
        } else if (wp == 9) {
            ImgCheckCovered();   // 圖片置頂：被工作列 / 遊戲視窗蓋住時重新置頂
        } else if (wp == 8) {
            HideToast();   // 圖示上方的提示顯示時間到
        } else if (wp == 2) {
            if (CursorOnTrayIcon()) ApplyTrayState();   // 仍停留在圖示上：更新提示
            else KillTimer(hwnd, 2);                    // 已離開：停止更新
        }
        return 0;
    case WM_DISPLAYCHANGE:
        ImgSyncAll();   // 螢幕解析度 / 數量改變：重新修正圖片的位置
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
    case WM_MENUSELECT: {
        UINT flags = HIWORD(wp);
        if (flags == 0xFFFF && lp == 0) {   // 選單已關閉
            HideMenuTip();
            break;
        }
        if (flags & (MF_POPUP | MF_SYSMENU)) {   // 子選單標題：不顯示提示
            HideMenuTip();
            break;
        }
        const wchar_t* tip = MenuTipText(LOWORD(wp));
        if (tip) ShowMenuTip((HMENU)lp, LOWORD(wp), tip);
        else HideMenuTip();
        break;
    }
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
    // 結束參數：ClientManager.exe /exit  要求正在執行的本工具正常結束 (讓它先還原遊戲的圖示、優先權與暫停狀態) 後離開；
    // 給 build.bat 重新建置前使用，避免強制終止造成遊戲狀態殘留
    if (wcsstr(GetCommandLineW(), L"/exit") != NULL) {
        HWND other = FindWindowW(L"MabinogiClientManagerClass", NULL);
        if (other) {
            DWORD opid = 0;
            GetWindowThreadProcessId(other, &opid);
            HANDLE hp = opid ? OpenProcess(SYNCHRONIZE, FALSE, opid) : NULL;
            PostMessageW(other, WM_CLOSE, 0, 0);
            if (hp) {
                WaitForSingleObject(hp, 8000);
                CloseHandle(hp);
            }
        }
        return 0;
    }
    if (wcsstr(GetCommandLineW(), L"/resume") != NULL) {
        ResumeAllClients();
        RecoverStaleIcons();   // 遊戲視窗若還留著藍色圖示也一併換回去
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

    CoInitializeEx(NULL, COINIT_APARTMENTTHREADED);   // ITaskbarList 需要
    INITCOMMONCONTROLSEX icc;
    icc.dwSize = sizeof(icc);
    icc.dwICC = ICC_WIN95_CLASSES;
    InitCommonControlsEx(&icc);   // 選單提示 (tooltips_class32) 需要
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
    RecoverStaleIcons();  // 以及還留著藍色圖示
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
    ImgSyncAll();
    StartMonitor();
    UpdateFpsSession();
    UpdateOverlayVisibility();

    MSG msg;
    while (GetMessageW(&msg, NULL, 0, 0) > 0) {
        TranslateMessage(&msg);
        DispatchMessageW(&msg);
    }

    ImgShutdown();
    ReleaseMouseClip();                              // 結束本工具前先放掉滑鼠範圍限制
    if (g_menuTip) DestroyWindow(g_menuTip);
    if (g_toastTip) DestroyWindow(g_toastTip);
    if (g_hideTaskbar) ApplyTaskbarButtons(false);   // 結束本工具前先恢復遊戲的工作列按鈕 (設定仍保留，下次啟動會再套用)
    ReleaseTaskbarList();
    CoUninitialize();
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
