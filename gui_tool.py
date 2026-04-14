import json
import time
import os
import subprocess
import threading
import random
import string
import cv2
import numpy as np

# Tắt xử lý đa luồng nội bộ của OpenCV. Rất quan trọng khi dùng Python threading (chạy nhiều máy)!
# Giúp khắc phục hoàn toàn lỗi rác RAM (Memory Fragmentation) và cv::OutOfMemoryError.
cv2.setNumThreads(1)

import customtkinter as ctk
from PIL import Image
import gc
import email.utils
from datetime import datetime, timedelta, timezone
import sys
import hashlib
import base64
import uuid
import urllib.request
import re
import imaplib
import email
from email.header import decode_header
try:
    import winreg
except ImportError:
    winreg = None


# Hàm hỗ trợ tìm đường dẫn file khi đóng gói .exe
def resource_path(relative_path):
    try:
        base_path = sys._MEIPASS
    except Exception:
        base_path = os.path.abspath(".")
    return os.path.join(base_path, relative_path)

IMAGE_CACHE = {}

def get_cached_image(path, grayscale=False):
    real_path = resource_path(path)
    if not os.path.exists(real_path): return None
    cache_key = path + ("_gray" if grayscale else "")
    if cache_key not in IMAGE_CACHE:
        # Sử dụng cv2 đã import ở trên đầu file
        img = cv2.imread(real_path, cv2.IMREAD_GRAYSCALE if grayscale else cv2.IMREAD_COLOR)
        if img is not None:
            IMAGE_CACHE[cache_key] = img
    return IMAGE_CACHE.get(cache_key)

# --- Security & Licensing ---
SECRET_KEY = "RyoUTE_MegaUpLvCF_2026"
LICENSE_FILE = "license.bin"

def get_hwid():
    try:
        def get_cmd(cmd):
            try:
                # Sử dụng shell=True và lọc kết quả sạch hơn
                res = subprocess.check_output(cmd, shell=True, creationflags=subprocess.CREATE_NO_WINDOW).decode().strip()
                lines = [l.strip() for l in res.split('\n') if l.strip()]
                if len(lines) > 1:
                    val = lines[1].strip()
                    # Loại bỏ các giá trị rác phổ biến của nhà sản xuất thường gây trùng mã
                    trash = ["filled", "default", "none", "00000000", "ffffffff", "unknown", "to be"]
                    if any(t in val.lower() for t in trash): return ""
                    return val
                return ""
            except: return ""

        # 1. BIOS UUID (Thường bị trùng trên máy ảo clone)
        hw_uuid = get_cmd("wmic csproduct get uuid")
        # 2. Disk Serial (Ổ cứng đầu tiên)
        disk_serial = get_cmd("wmic diskdrive where 'index=0' get serialnumber")
        # 3. CPU ID
        cpu_id = get_cmd("wmic cpu get processorid")
        # 4. Mainboard Serial (Rất khó trùng trên máy thật)
        board_serial = get_cmd("wmic baseboard get serialnumber")
        
        # 5. Machine GUID (Duy nhất cho mỗi bộ Windows cài đặt)
        machine_guid = ""
        if winreg:
            try:
                registry_key = winreg.OpenKey(winreg.HKEY_LOCAL_MACHINE, r"SOFTWARE\Microsoft\Cryptography", 0, winreg.KEY_READ | winreg.KEY_WOW64_64KEY)
                machine_guid, _ = winreg.QueryValueEx(registry_key, "MachineGuid")
                winreg.CloseKey(registry_key)
            except: pass

        # 6. MAC Address (Dùng làm định danh bổ trợ)
        mac = str(uuid.getnode())

        # Kết hợp tất cả các nguồn dữ liệu để tạo mã băm 20 ký tự
        combined = f"U:{hw_uuid}|D:{disk_serial}|C:{cpu_id}|B:{board_serial}|G:{machine_guid}|M:{mac}"
        return hashlib.sha256(combined.encode()).hexdigest()[:20].upper()
    except:
        # Fallback an toàn nếu toàn bộ các lệnh trên lỗi
        return hashlib.sha256(str(uuid.getnode()).encode()).hexdigest()[:20].upper()


def verify_license(key, hwid):
    try:
        # Format key: Base64(ExpiryTimestamp|Signature)
        decoded = base64.b64decode(key).decode()
        expiry_str, signature = decoded.split('|')
        
        # Kiểm tra Signature
        expected_sig = hashlib.sha256(f"{expiry_str}{hwid}{SECRET_KEY}".encode()).hexdigest()[:10]
        if signature != expected_sig:
            return False, "Key không hợp lệ cho máy này!"
        
        # Kiểm tra Hạn dùng (Chính xác đến từng giây)
        expiry_date = datetime.strptime(expiry_str, "%Y-%m-%d %H:%M:%S")
        if datetime.now() > expiry_date:
            return False, f"Key đã hết hạn vào {expiry_str}!"
            
        return True, expiry_str
    except:
        return False, "Key sai định dạng!"

# Công cụ nhanh cho Admin để tạo Key (Bạn có thể bỏ vào file riêng)
# def generate_key(hwid, days):
#     expiry = (datetime.now() + timedelta(days=days)).strftime("%Y-%m-%d")
#     sig = hashlib.sha256(f"{expiry}{hwid}{SECRET_KEY}".encode()).hexdigest()[:10]
#     full_key = base64.b64encode(f"{expiry}|{sig}".encode()).decode()
#     return full_key

# --- Theme Configuration ---
ctk.set_appearance_mode("Dark")
ctk.set_default_color_theme("blue")

NAV_COLOR = "#0F0F0F"
BG_COLOR = "#121212"
CARD_COLOR = "#1D1D1D"
ACCENT_GREEN = "#00D2FF"
ACCENT_PURPLE = "#A855F7"
ACCENT_RED = "#EF4444"

# --- Logic Backend (AutoClicker - Hỗ trợ Single Instance) ---

class AutoClickerInstance:
    def __init__(self, device_id, adb_path, ld_path, log_func, update_ui_func):
        self.device_id = device_id
        self.adb_path = adb_path
        self.ld_path = ld_path # Lưu đường dẫn LDPlayer được truyền vào
        self.log_func = log_func
        self.update_ui_func = update_ui_func
        self.running = False
        # Tasks list: Each task is {name, script, interval, max_runs, current_runs, next_run}
        self.tasks = []
        self.current_task_index = -1
        
        # Default initialization (will be overridden by UI/config)
        self.add_task("Main Task", [
             {"action": "click_image", "target": "images/game_logo.png", "timeout": 30, "confidence": 0.8},
             {"action": "zoom_out_max"},
        ], interval=60, max_runs=1)
        
        self.codes_queue = [] 
        
        # Scheduling settings
        self.repeat_count = 1        # -1 for infinite
        self.interval_seconds = 60
        self.runs_completed = 0
        self.next_run_time = 0

    def log(self, msg):
        self.log_func(f"[{self.device_id}] {msg}")

    def escape_adb_text(self, text):
        if not text: return ""
        chars_to_escape = ['\\', '"', "'", '&', '>', '<', '|', ';', '(', ')', '*', '?', '$', '!', '#', '%', '{', '}', '~', '[', ']', '^', '@']
        escaped_text = ""
        for char in text:
            if char == ' ': escaped_text += "%s"
            elif char in chars_to_escape: escaped_text += f"\\{char}"
            else: escaped_text += char
        return escaped_text

    def update_status(self, status, is_lagging=None):
        self.status = status
        if is_lagging is not None:
            self.is_lagging = is_lagging
        self.update_ui_func()

    def call_adb(self, args, timeout=15):
        cmd = [self.adb_path, "-s", self.device_id] + args
        try:
            # Thêm timeout để tránh treo luồng nếu máy ảo bị đơ
            return subprocess.run(cmd, capture_output=True, timeout=timeout, creationflags=subprocess.CREATE_NO_WINDOW)
        except subprocess.TimeoutExpired:
            self.log(f"ADB TIMEOUT: Lệnh {args[0] if args else ''} quá lâu.")
            return subprocess.CompletedProcess(cmd, 1, b"", b"timeout")
        except Exception as e:
            return subprocess.CompletedProcess(cmd, 1, b"", str(e).encode())

    def get_screenshot(self):
        try:
            # Ưu tiên dùng exec-out để nhận byte chuẩn
            cmd = [self.adb_path, "-s", self.device_id, "exec-out", "screencap", "-p"]
            process = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, creationflags=subprocess.CREATE_NO_WINDOW)
            try:
                stdout, _ = process.communicate(timeout=10)
            except subprocess.TimeoutExpired:
                process.kill()
                return None
            
            if process.returncode != 0 or not stdout:
                # Chế độ dự phòng
                cmd = [self.adb_path, "-s", self.device_id, "shell", "screencap", "-p"]
                process = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, creationflags=subprocess.CREATE_NO_WINDOW)
                try:
                    stdout, _ = process.communicate(timeout=15)
                except subprocess.TimeoutExpired:
                    process.kill()
                    return None
                    
                if process.returncode != 0 or not stdout: return None
                stdout = stdout.replace(b"\r\n", b"\n")
            
            image_array = np.frombuffer(stdout, dtype=np.uint8)
            img = cv2.imdecode(image_array, cv2.IMREAD_COLOR)
            
            del image_array
            del stdout
            return img
        except: return None

    def execute_step(self, step):
        if not self.running: return False
        action = step.get("action")
        self.last_step_time = time.time()
        res = True
        
        if action == "click_image":
            res = self.click_image_logic(step)
        elif action == "click_image_if":
            self.click_image_logic(step)
            res = True
        elif action == "zoom_out_max":
            res = self.zoom_out_max_logic()
        elif action == "loop_cases":
            res = self.loop_cases_logic(step)
        elif action == "if_exists":
            res = self.if_exists_logic(step)
        elif action == "click_any":
            res = self.click_any_logic(step)
        elif action == "wait":
            wait_time = step.get("duration") or step.get("timeout") or 1
            time.sleep(wait_time)
            res = True
        
        # Kiểm tra lag: Nếu 1 bước mất hơn 35s
        duration = time.time() - self.last_step_time
        if duration > 35: 
             self.update_status(self.status, True)
        else:
             self.update_status(self.status, False)

        return res

    def zoom_out_max_logic(self):
        self.log("HÀNH ĐỘNG: Zoom Out (Dùng lệnh điều khiển LDPlayer)...")
        try:
            port_match = re.search(r'(\d+)', self.device_id)
            if not port_match: return False
            port = int(port_match.group(1))
            idx = (port - 5554) // 2
            
            ld_console = self.ld_path
            if ld_console and os.path.isdir(ld_console):
                ld_console = os.path.join(ld_console, "ldconsole.exe")
            elif ld_console and not ld_console.lower().endswith("ldconsole.exe"):
                ld_dir = os.path.dirname(ld_console)
                ld_console = os.path.join(ld_dir, "ldconsole.exe")

            if os.path.exists(ld_console):
                self.log(f"Đang gọi ldconsole Index {idx} thực hiện ZoomOut...")
                for _ in range(8):
                    if not self.running: break
                    subprocess.run([ld_console, "action", "--index", str(idx), "--key", "zoomOut"], creationflags=subprocess.CREATE_NO_WINDOW)
                    time.sleep(0.2)
                return True
        except Exception as e:
            self.log(f"LỖI Zoom: {e}")

        self.log("DỰ PHÒNG: Thử ZoomOut bằng phím tắt hệ thống...")
        self.call_adb(["shell", "input keyevent 169"]) # KEYCODE_ZOOM_OUT
        return True

    def setup_tasks(self):
        """
        HÀM CẤU HÌNH NHIỆM VỤ: Bạn chỉnh sửa kịch bản tại đây.
        """
        self.tasks = [] # Xóa sạch các task cũ trước khi nạp mới

        # --- MẪU 1: TÁC VỤ CHẠY 1 LẦN (Ví dụ: Nhận quà khởi tạo) ---
        self.add_task(
            name="Khởi tạo", 
            script=[
                {"action": "wait", "timeout": 2}
            ], 
            max_runs=1 # Chạy xong 1 lần tự xóa
        )

        # Task 1: Thuê Ngọc Trai
        self.add_task(
            name="Thuê Ngọc Trai", 
            script=[
                {"action": "click_image", "target": "images/ngoc_trai1.png", "timeout": 10},
                {"action": "click_image_if", "target": "images/thu_hoach.png", "timeout": 3},
                {"action": "loop_cases",
                    "cases": [
                        {
                            "trigger": "images/plus.png",
                            "script": [
                                {"action": "click_image", "target": "images/plus.png"},
                                {"action": "click_image", "target": "images/thue.png", "timeout": 10},
                                {"action": "wait", "timeout": 2},
                                {"action": "click_image_if", "target": "images/xac_nhan1.png", "timeout": 5},
                                {"action": "click_image_if", "target": "images/space.png", "timeout": 5},
                            ]
                        },
                        {
                             "trigger": "images/plus1.png",
                             "script": [
                                {"action": "click_image", "target": "images/plus.png"},
                                {"action": "click_image", "target": "images/thue.png", "timeout": 10},
                                {"action": "wait", "timeout": 2},
                                {"action": "click_image_if", "target": "images/xac_nhan1.png", "timeout": 5},
                                {"action": "click_image_if", "target": "images/space.png", "timeout": 5},
                            ]
                        }

                    ]
                },
                {"action": "click_image_if", "target1": "images/x.png", "target2": "images/x2.png", "timeout": 5},

            ], 
            interval=60*60*2, # 1 phút 1 giây
            max_runs=-1  # -1 là lặp vô tận
        )

        # Task 2: Trồng hoa tươi trong hội
        self.add_task(
            name="Trồng hoa tươi trong hội", 
            script=[
                {"action": "click_image", "target": "images/hoi.png",  "timeout": 20},
                {"action": "click_image_if", "target1": "images/x.png", "target2": "images/x2.png", "timeout": 5},
                {"action": "click_image", "target": "images/trong_hoa_tuoi.png",  "timeout": 20},
                {"action": "click_image", "target": "images/tat_ca_thu_hoach.png",  "timeout": 20},
                {"action": "wait", "timeout": 3},
                {"action": "click_image", "target": "images/thoat_trong_cay.png",  "timeout": 20},
                {"action": "wait", "timeout": 2},
                {"action": "click_image", "target": "images/thoat_hoi.png",  "timeout": 20},

            ], 
            interval=60*60*1.5, 
            max_runs=-1
        )
        # Task 3: Mua ở Shop
        self.add_task(
            name="Lấy vàng trong shop", 
            script=[
                {"action": "click_image", "target": "images/multi.png",  "timeout": 20},
                {"action": "click_image", "target": "images/tiem1.png",  "timeout": 20},
                {"action": "wait", "timeout": 5},
                {"action": "click_image", "target": "images/tiem_nguyen_lieu.png",  "timeout": 20},
                {"action": "wait", "timeout": 2},
                {"action": "click_image", "target": "images/mua_nhanh.png",  "timeout": 20},
                {"action": "wait", "timeout": 3},
                
                {"action": "click_image_if", "target": "images/xac_nhan1.png",  "timeout": 5},
                {"action": "wait", "timeout": 5},

                {"action": "click_image", "target": "images/thoat_tiem.png",  "timeout": 20},
            ], 
            interval=60*60*2.5, 
            max_runs=-1
        )
        # Task 4: Giao hàng cư dân
        self.add_task(
            name="Giao hàng cư dân", 
            script=[
                {"action": "click_image", "target": "images/nhiem_vu2.jpg",  "timeout": 20},
                {"action": "click_image", "target": "images/item1.png",  "timeout": 20},
                {"action": "click_image", "target": "images/gui.png",  "timeout": 20},
                {"action": "wait", "timeout": 3},
                {"action": "click_image", "target": "images/item2.png",  "timeout": 20},
                {"action": "click_image", "target": "images/gui.png",  "timeout": 20},
                {"action": "wait", "timeout": 3},
                {"action": "click_image_if", "target": "images/muon_xiu.png",  "timeout": 5},
                {"action": "click_image_if", "target": "images/xac_nhan1.png",  "timeout": 3},
                
                {"action": "click_image", "target": "images/x1.png",  "timeout": 20},
            ], 
            
            interval=66, 
            max_runs=100
        )

        # Task 5: Giao hàng tại sảnh (Xử lý Đỏ, Vàng, Xanh)
        self.add_task(
            name="Giao hàng tại sảnh", 
            script=[
                {
                    "action": "loop_cases",
                    "cases": [
                        {
                            "trigger": "images/do1.png",
                            "script": [
                                {"action": "click_image", "target": "images/do1.png"},
                                {"action": "wait", "timeout": 2},
                                {"action": "click_image", "target": "images/chua_co_hang.png"}
                            ]
                        },
                        {
                            "trigger": "images/vang1.png",
                            "script": [
                                {"action": "click_image", "target": "images/vang1.png"},
                                {"action": "wait", "timeout": 2},
                                {
                                    "action": "if_exists",
                                    "target": "images/den_lam.png",
                                    "timeout": 3,
                                    "script": [
                                        {"action": "click_image", "target": "images/den_lam.png"},
                                        {"action": "wait", "timeout": 2},
                                        {"action": "click_image", "target": "images/lam.png"},
                                        {"action": "wait", "timeout": 5},
                                        {"action": "click_image", "target": "images/xac_nhan.png"},
                                        {"action": "click_any", "timeout": 3},
                                        {"action": "wait", "timeout": 5},
                                        {"action": "click_image", "target": "images/giao.png"},
                                        {"action": "click_any", "timeout": 3}
                                    ]
                                },
                                {
                                    "action": "if_exists",
                                    "target": "images/next.png",
                                    "timeout": 3,
                                    "script": [
                                        {"action": "click_image", "target": "images/bo_qua.png"},
                                        {"action": "wait", "timeout": 2},
                                        {"action": "click_any", "timeout": 3},
                                    ]
                                },
                                {
                                    "action": "if_exists",
                                    "target": "images/x.png","target2": "images/x2.png","target3": "images/x5.jpg",
                                    "timeout": 3,
                                    "script": [
                                        {"action": "click_image", "target": "images/x.png", "target2": "images/x2.png","target3": "images/x5.jpg"},
                                        {"action": "wait", "timeout": 2},
                                        
                                    ]
                                }
                            ]
                        },
                        {
                            "trigger": "images/xanh1.png",
                            
                            "script": [
                                {"action": "click_image", "target": "images/xanh1.png"},
                                {"action": "click_image", "target": "images/giao.png"},
                                {"action": "click_any", "timeout": 3},
                                {
                                    "action": "if_exists",
                                    "target": "images/next.png",
                                    "timeout": 3,
                                    "script": [
                                        {"action": "click_image", "target": "images/xanh1.png"},
                                        {"action": "wait", "timeout": 2},
                                        {"action": "click_image", "target": "images/nhan.png"},
                                        {"action": "click_image", "target": "images/xx.png"},
                                    ]
                                },
                            ]
                        }
                    ]
                }
            ], 
            interval=120, 
            max_runs=-1
        )

    def loop_cases_logic(self, step):
        cases = step.get("cases", [])
        if not cases: return True
        
        while self.running:
            found_any = False
            screen = self.get_screenshot()
            if screen is None: 
                time.sleep(1)
                continue
            
            for case in cases:
                trigger = case.get("trigger")
                sub_script = case.get("script", [])
                
                # Kiểm tra xem trigger có trên màn hình không
                t_img = get_cached_image(trigger)
                if t_img is None: continue
                
                res = cv2.matchTemplate(screen, t_img, cv2.TM_CCOEFF_NORMED)
                _, max_val, _, _ = cv2.minMaxLoc(res)
                del res
                
                if max_val >= 0.8:
                    self.log(f"PHÁT HIỆN: {os.path.basename(trigger)} (Độ khớp: {max_val:.2f})")
                    found_any = True
                    # Thực hiện kịch bản con của trường hợp này
                    for s_step in sub_script:
                        if not self.running: break
                        self.execute_step(s_step)
                    break # Thoát vòng for để quét lại từ đầu (đảm bảo ưu tiên)
            
            del screen
            if not found_any:
                self.log("HỆ THỐNG: Đã xử lý hết tất cả các trường hợp.")
                break
            time.sleep(1)
        return True

    def if_exists_logic(self, step):
        target = step.get("target")
        sub_script = step.get("script", [])
        timeout = step.get("timeout", 0) # Mặc định là 0 (quét 1 lần duy nhất)
        if not target: return True
        
        start_time = time.time()
        found = False
        
        while self.running:
            screen = self.get_screenshot()
            if screen is None: 
                time.sleep(0.5)
                if time.time() - start_time > timeout: break
                continue
            
            t_img = get_cached_image(target)
            if t_img is None: 
                del screen
                break
                
            res = cv2.matchTemplate(screen, t_img, cv2.TM_CCOEFF_NORMED)
            _, max_val, _, _ = cv2.minMaxLoc(res)
            del res
            del screen
            
            if max_val >= 0.8:
                found = True
                break
            
            # Nếu hết thời gian chờ
            if time.time() - start_time > timeout:
                break
            time.sleep(0.5)
            
        if found:
            self.log(f"ĐIỀU KIỆN ĐÚNG: Tìm thấy {os.path.basename(target)}, thực hiện kịch bản con...")
            for s_step in sub_script:
                if not self.running: break
                self.execute_step(s_step)
            return True
        else:
            if timeout > 0:
                self.log(f"ĐIỀU KIỆN SAI: Chờ {timeout}s không thấy {os.path.basename(target)}, bỏ qua.")
            else:
                self.log(f"ĐIỀU KIỆN SAI: Không thấy {os.path.basename(target)} (Quét tức thì), bỏ qua.")
            return True

    def click_any_logic(self, step):
        delay = step.get("timeout", 0)
        if delay > 0:
            self.log(f"HỆ THỐNG: Chờ {delay}s trước khi click...")
            time.sleep(delay)
        
        # Lấy kích thước màn hình
        screen = self.get_screenshot()
        if screen is not None:
            h, w = screen.shape[:2]
            cx, cy = w // 2, h // 3
            self.call_adb(["shell", "input", "tap", str(cx), str(cy)])
            self.log(f"CLICK ANY: Toạ độ ({cx}, {cy})")
            del screen
            return True
        return False

    def click_image_logic(self, step):
        targets = []
        if step.get("target"): targets.append(step.get("target"))
        i = 1
        while f"target{i}" in step:
            targets.append(step.get(f"target{i}"))
            i += 1
        
        timeout = step.get("timeout", 10)
        confidence = step.get("confidence", 0.8)
        
        target_imgs = []
        for t_path in targets:
            img = get_cached_image(t_path, grayscale=False)
            if img is not None: 
                target_imgs.append((t_path, img))
            else:
                self.log(f"LỖI: Không tìm thấy ảnh mẫu: {t_path}")

        start = time.time()
        # Pre-fetch templates outside the loop to save CPU and RAM lookups
        prepared_targets = []
        for t_path in targets:
            t_img = get_cached_image(t_path, grayscale=False)
            if t_img is not None:
                prepared_targets.append((t_path, t_img))

        while time.time() - start < timeout and self.running:
            screen = self.get_screenshot()
            if screen is not None:
                # cv2.imwrite(f"debug_{self.device_id}.png", screen) # Tắt ghi file liên tục để giảm lag disk
                
                for t_path, t_img in prepared_targets:
                    res = cv2.matchTemplate(screen, t_img, cv2.TM_CCOEFF_NORMED)
                    _, max_val, _, max_loc = cv2.minMaxLoc(res)
                    
                    # Giải phóng matrix kết quả ngay khi xong
                    del res
                    
                    if max_val >= confidence:
                        th, tw = t_img.shape[:2]
                        cx, cy = max_loc[0] + tw//2, max_loc[1] + th//2
                        self.call_adb(["shell", "input", "tap", str(cx), str(cy)])
                        self.log(f"CLICK: {os.path.basename(t_path)} (Khớp: {max_val:.2f})")
                        del screen
                        return True
                    else:
                        if max_val > 0.4:
                            self.log(f"TRƯỢT: {os.path.basename(t_path)} khớp {max_val:.2f} (Cần {confidence})")
                
                del screen # Giải phóng screenshot cũ trước khi loop tiếp
            time.sleep(1)
        return False

    def add_task(self, name, script, interval=60, max_runs=-1):
        self.tasks.append({
            "name": name,
            "script": script,
            "interval": interval,
            "max_runs": max_runs,
            "current_runs": 0,
            "next_run": time.time()
        })

    def run(self):
        self.running = True
        self.log(f"HỆ THỐNG: Bất đầu trình quản lý đa tác vụ ({len(self.tasks)} tác vụ).")
        
        while self.running:
            now = time.time()
            # 1. Tìm tất cả các tác vụ đang đến hạn (hoặc quá hạn)
            due_tasks = []
            next_task_time = float('inf')
            
            for task in self.tasks[:]:
                if task["max_runs"] == -1 or task["current_runs"] < task["max_runs"]:
                    if now >= task["next_run"]:
                        due_tasks.append(task)
                    elif task["next_run"] < next_task_time:
                        next_task_time = task["next_run"]
                else:
                    if task in self.tasks: self.tasks.remove(task)
            
            # 2. Nếu có tác vụ đến hạn, chọn tác vụ "quá hạn" lâu nhất để làm trước
            if due_tasks:
                # Sắp xếp: Tác vụ nào có 'next_run' nhỏ nhất (đến hạn sớm nhất) sẽ đứng đầu
                due_tasks.sort(key=lambda x: x["next_run"])
                task = due_tasks[0]
                
                self.log(f"--- TÁC VỤ: {task['name']} (Lần {task['current_runs'] + 1}) ---")
                self.update_status(f"Chạy {task['name']}")
                
                # Thực thi các bước
                success = True
                for step in task["script"]:
                    if not self.running: break
                    if not self.execute_step(step):
                        self.log(f"CẢNH BÁO: Tác vụ '{task['name']}' lỗi.")
                        success = False
                        break
                
                if success:
                    self.log(f"HOÀN TẤT: {task['name']} - Lần {task['current_runs'] + 1}")
                
                task["current_runs"] += 1
                
                # Thiết lập lượt chạy tiếp theo
                if task["max_runs"] != -1 and task["current_runs"] >= task["max_runs"]:
                    self.log(f"HẾT LƯỢT: Tác vụ '{task['name']}' đã xong.")
                    if task in self.tasks: self.tasks.remove(task)
                else:
                    # Lượt tiếp theo tính từ lúc Task này vừa xong để đảm bảo khoảng cách an toàn
                    task["next_run"] = time.time() + task["interval"]
                
                gc.collect()
                # Sau khi xong 1 task, quay lại đầu loop while để kiểm tra ngay các task đang đợi khác
                continue 
            
            # 3. Nếu không có task nào đến hạn, kiểm tra xem còn task nào trong tương lai không
            if not self.tasks:
                self.log("HỆ THỐNG: Mọi tác vụ đã kết thúc.")
                break
                
            # Cập nhật trạng thái chờ cho UI
            if self.running:
                wait_time = int(next_task_time - time.time())
                if wait_time > 0:
                    mins, secs = divmod(wait_time, 60)
                    hrs, mins = divmod(mins, 60)
                    time_str = f"{hrs:02d}:{mins:02d}:{secs:02d}" if hrs > 0 else f"{mins:02d}:{secs:02d}"
                    self.update_status(f"Chờ {time_str}")
                else:
                    self.update_status("Chuẩn bị...")

            time.sleep(1)
            
        self.running = False
        self.log("HỆ THỐNG: Máy đã dừng hoàn toàn.")
        self.update_ui_func()

# --- Modern UI (Premium Edition) ---

class MultiPremiumApp(ctk.CTk):
    def __init__(self):
        super().__init__()
        self.title("MegaUpLvCFTool(LD)")
        self.geometry("1100x850")
        self.configure(fg_color=BG_COLOR)
        
        self.active_workers = [] # Các thread đang chạy
        self.instances = [] # Danh sách các máy thực tế đang chạy ADB
        self.adb_path = self.find_adb()
        self.ld_path = r"C:\LDPlayer\LDPlayer9\ldconsole.exe" # Mặc định
        
        # Assets (Sử dụng resource_path để đóng gói)
        self.logo_img = ctk.CTkImage(Image.open(resource_path("logo.png")), size=(80, 80))
        self.start_icon = ctk.CTkImage(Image.open(resource_path("start.png")), size=(25, 25))
        self.stop_icon = ctk.CTkImage(Image.open(resource_path("stop.png")), size=(25, 25))

        self.setup_layout()
        self.load_config() # Tải đường dẫn đã lưu
        self.scan_devices()

    def find_adb(self):
        paths = ["adb", r"C:\LDPlayer\LDPlayer9\adb.exe", r"C:\LDPlayer\LDPlayer4\adb.exe"]
        for p in paths:
            try:
                subprocess.run([p, "version"], capture_output=True, check=True, creationflags=subprocess.CREATE_NO_WINDOW)
                return p
            except: continue
        return "adb"

    def setup_layout(self):
        # 1. Sidebar
        self.sidebar = ctk.CTkFrame(self, width=280, corner_radius=0, fg_color=NAV_COLOR)
        self.sidebar.pack(side="left", fill="y")
        
        ctk.CTkLabel(self.sidebar, image=self.logo_img, text="").pack(pady=(40,0))
        self.logo_label = ctk.CTkLabel(self.sidebar, text="BẢNG ĐIỀU KHIỂN", font=ctk.CTkFont(size=22, weight="bold"), text_color=ACCENT_GREEN)
        self.logo_label.pack(pady=(20, 0))
        ctk.CTkLabel(self.sidebar, text="MegaUpLvCFTool(LD) v2.5", font=ctk.CTkFont(size=12)).pack(pady=(0, 20))

        # LDPlayer Path Config
        self.path_card = ctk.CTkFrame(self.sidebar, fg_color=CARD_COLOR, corner_radius=10)
        self.path_card.pack(padx=20, pady=5, fill="x")
        ctk.CTkLabel(self.path_card, text="ĐƯỜNG DẪN LDPLAYER", font=ctk.CTkFont(size=11, weight="bold")).pack(pady=(5, 0))
        self.ld_path_entry = ctk.CTkEntry(self.path_card, placeholder_text="Ví dụ: C:\LDPlayer\LDPlayer9", height=30)
        self.ld_path_entry.pack(padx=10, pady=5, fill="x")
        self.ld_path_entry.insert(0, r"C:\LDPlayer\LDPlayer9")
        
        self.save_button = ctk.CTkButton(self.path_card, text="Lưu Cấu Hình", command=self.save_config, height=30)
        self.save_button.pack(padx=10, pady=10, fill="x")


        # Control
        self.btn_start = ctk.CTkButton(self.sidebar, text=" CHẠY TẤT CẢ", image=self.start_icon, compound="left", command=self.start_all, height=50, corner_radius=10, font=ctk.CTkFont(size=16, weight="bold"))
        self.btn_start.pack(padx=20, pady=(30, 10), fill="x")
        self.btn_stop = ctk.CTkButton(self.sidebar, text=" DỪNG TẤT CẢ", image=self.stop_icon, compound="left", command=self.stop_all, fg_color="#333", height=50, corner_radius=10)
        self.btn_stop.pack(padx=20, pady=10, fill="x")

        # Credit Footer
        ctk.CTkLabel(self.sidebar, text="Nguồn: RyoUTE - 0393203161", font=ctk.CTkFont(size=11), text_color="#666").pack(side="bottom", pady=20)

        # 2. Main Area
        self.main_content = ctk.CTkFrame(self, fg_color="transparent")
        self.main_content.pack(side="right", fill="both", expand=True, padx=25, pady=25)

        # Instance Selection Card
        self.inst_frame = ctk.CTkFrame(self.main_content, fg_color=CARD_COLOR, corner_radius=15, border_width=1, border_color="#333")
        self.inst_frame.pack(fill="x", pady=(0, 20))
        inst_header = ctk.CTkFrame(self.inst_frame, fg_color="transparent")
        inst_header.pack(fill="x", padx=20, pady=10)
        ctk.CTkLabel(inst_header, text="THIẾT BỊ ĐANG MỞ", font=ctk.CTkFont(size=14, weight="bold"), text_color=ACCENT_GREEN).pack(side="left")

        # Action Buttons for Instances
        btns_frame = ctk.CTkFrame(inst_header, fg_color="transparent")
        btns_frame.pack(side="right")
        # Nút chọn tất cả được gỡ bỏ vì người dùng muốn chạy tất cả máy mà không cần check
        self.btn_refresh = ctk.CTkButton(btns_frame, text="Làm Mới Danh Sách", command=self.scan_devices, height=26, width=120, font=ctk.CTkFont(size=11, weight="bold"))
        self.btn_refresh.pack(side="left", padx=5)

        self.device_list_frame = ctk.CTkScrollableFrame(self.inst_frame, height=180, fg_color="transparent") 
        self.device_list_frame.pack(fill="x", padx=10, pady=(0, 15))
        # Tăng số cột lên 12 và cấu hình cột đều nhau
        for col in range(12): 
            self.device_list_frame.grid_columnconfigure(col, weight=1)
        self.device_cards = {}


        # View Area
        self.view_card = ctk.CTkFrame(self.main_content, fg_color=CARD_COLOR, corner_radius=15)
        self.view_card.pack(fill="both", expand=True)
        
        # Log Display
        self.log_textbox = ctk.CTkTextbox(self.view_card, font=("Consolas", 12), fg_color="#000", border_width=1, border_color="#333")
        self.log_textbox.pack(fill="both", expand=True, padx=15, pady=15)

    def update_all_ui(self):
        def _update():
            # Cập nhật trạng thái từng máy trên card
            for worker in self.active_workers:
                if worker.device_id in self.device_cards:
                    color = "#22D3EE" if worker.running else "#888" # Cyan for running
                    if worker.is_lagging: color = "#FB923C" # Orange for lag
                    if worker.status == "Xong": color = "#4ADE80" # Green for done
                    
                    self.device_cards[worker.device_id]["status"].configure(
                        text=worker.status, 
                        text_color=color
                    )
        self.after(0, _update)

    def save_config(self):
        ld_path = self.ld_path_entry.get().strip()
        config = {
            "ld_path": ld_path,
        }
        with open("config.json", "w") as f:
            json.dump(config, f)
        if ld_path:
            self.ld_path = ld_path
        self.add_log("HỆ THỐNG: Đã lưu cấu hình.")

    def load_config(self):
        if os.path.exists("config.json"):
            try:
                with open("config.json", "r") as f:
                    config = json.load(f)
                    path = config.get("ld_path", "")
                    if path:
                        self.ld_path_entry.delete(0, "end")
                        self.ld_path_entry.insert(0, path)
                        self.ld_path = path
            except: pass

    def scan_devices(self):
        # Disable button to prevent multiple scans
        if hasattr(self, "btn_refresh"):
            self.btn_refresh.configure(state="disabled", text="Đang Quét...")
        
        base_path = self.ld_path_entry.get().strip()
        threading.Thread(target=self._perform_scan, args=(base_path,), daemon=True).start()

    def _perform_scan(self, base_path):
        # Determine ADB path
        adb_path = os.path.join(base_path, "adb.exe")
        if not os.path.exists(adb_path): 
            alt_path = os.path.join(base_path, "LDPlayer9", "adb.exe")
            if os.path.exists(alt_path):
                adb_path = alt_path
            else:
                adb_path = "adb"
        
        device_serials = []
        offline_count = 0
        unauthorized_count = 0
        
        try:
            # CHÚ Ý: Không kill-server mỗi lần quét vì sẽ làm ngắt kết nối các máy đang chạy.
            
            # Chỉ chạy lệnh adb devices để lấy danh sách thiết bị thực tế đang có
            res = subprocess.run([adb_path, "devices"], capture_output=True, text=True, timeout=10, creationflags=subprocess.CREATE_NO_WINDOW)
            
            # Nếu ADB server chưa chạy, subprocess sẽ tự động start nó. 
            # Chỉ khi lỗi nặng mới cần kill-server thủ công.
            
            lines = res.stdout.strip().split('\n')
            for line in lines:
                line = line.strip()
                if not line or "List of devices attached" in line or "* daemon" in line:
                    continue
                
                parts = line.split() # Dùng split() để tách mọi loại khoảng trắng (tab/space)
                if len(parts) >= 2:
                    serial = parts[0].strip()
                    status = parts[1].strip()
                    
                    if status == "device":
                        device_serials.append(serial)
                    elif status == "offline":
                        offline_count += 1
                    elif status == "unauthorized":
                        unauthorized_count += 1
            
        except Exception as e:
            self.add_log(f"LỖI: Không thể quét thiết bị: {str(e)}")
            
        # Log kết quả chi tiết để user biết tại sao thiếu máy
        if offline_count > 0 or unauthorized_count > 0:
            self.add_log(f"HỆ THỐNG: Tìm thấy {len(device_serials)} máy OK, {offline_count} máy offline, {unauthorized_count} máy chưa xác thực.")
            self.add_log("Gợi ý: Hãy kiểm tra các máy chưa nhận được xem đã bật 'Gỡ lỗi ADB' chưa.")
            
        # Update UI on main thread
        self.after(0, lambda: self._update_device_list_ui(device_serials, adb_path))

    def _update_device_list_ui(self, device_serials, adb_path):
        self.adb_path = adb_path
        
        # Clear existing widgets
        for w in self.device_list_frame.winfo_children():
            w.destroy()
        self.device_cards = {}
        
        # Create new widgets
        for i, serial in enumerate(device_serials):
            card = ctk.CTkFrame(self.device_list_frame, fg_color="#252525", corner_radius=6, border_width=1, border_color="#383838")
            # Sắp xếp 12 máy trên 1 hàng để tối ưu không gian
            card.grid(row=i // 12, column=i % 12, padx=3, pady=3, sticky="nsew")
            
            # Tách lấy port hoặc phần số cuối cùng của Serial (Ví dụ: emulator-5554 -> 5554, 127.0.0.1:5556 -> 5556)
            display_name = serial.replace("emulator-", "").split(":")[-1]
            name_lbl = ctk.CTkLabel(card, text=display_name, font=ctk.CTkFont(size=10, weight="bold"))
            name_lbl.pack(pady=(5, 0))
            
            status_lbl = ctk.CTkLabel(card, text="Sẵn sàng", font=ctk.CTkFont(size=9), text_color="#666")
            status_lbl.pack(pady=(0, 5))
            
            self.device_cards[serial] = {"card": card, "status": status_lbl}

        if not self.device_cards:
            self.add_log("CẢNH BÁO: Không tìm thấy thiết bị nào đang chạy. Vui lòng kiểm tra đã Mở LDPlayer và bật 'Gỡ lỗi ADB' trong Cài đặt LDPlayer.")
        else:
            self.add_log(f"HỆ THỐNG: Đã tìm thấy {len(self.device_cards)} thiết bị.")
            
        # Re-enable button
        if hasattr(self, "btn_refresh"):
            self.btn_refresh.configure(state="normal", text="Làm Mới Danh Sách")

    def add_log(self, text):
        timestamp = datetime.now().strftime("%H:%M:%S")
        msg = f"[{timestamp}] {text}"
        print(msg)
        if hasattr(self, "log_textbox"):
             # Tự động xóa bớt log cũ nếu quá dài (> 2000 dòng) để tránh tràn RAM
             log_content = self.log_textbox.get("1.0", "end")
             if log_content.count("\n") > 2000:
                 self.log_textbox.delete("1.0", "500.0") # Xóa 500 dòng đầu
                 self.log_textbox.insert("1.0", "--- ĐÃ XÓA LOG CŨ ĐỂ TIẾT KIỆM RAM ---\n")
                 
             self.log_textbox.insert("end", msg + "\n")
             self.log_textbox.see("end")

    def start_all(self):
        # Kiểm tra Hạn dùng trước khi chạy
        if os.path.exists(LICENSE_FILE):
             with open(LICENSE_FILE, "r") as f:
                saved_key = f.read().strip()
             valid, msg = verify_license(saved_key, get_hwid())
             if not valid:
                 # Hết hạn hoặc sai mã -> Mở lại Login
                 self.destroy()
                 LoginApp().mainloop()
                 return
        else:
             self.destroy()
             LoginApp().mainloop()
             return

        selected_serials = list(self.device_cards.keys()) 
        if not selected_serials:
            self.add_log("LỖI: Không tìm thấy thiết bị nào để chạy.")
            return

        self.btn_start.configure(state="disabled", text=" ĐANG CHẠY...")
        self.btn_stop.configure(state="normal", fg_color=ACCENT_RED)
        
        self.active_workers = []
        for serial in selected_serials:
            worker = AutoClickerInstance(
                serial,
                self.adb_path,
                self.ld_path,
                self.add_log,
                self.update_all_ui
            )
            
            # Nạp tất cả kịch bản từ hàm config riêng
            worker.setup_tasks()

            self.active_workers.append(worker)
            t = threading.Thread(target=worker.run, args=(), daemon=True)
            t.start()

    def stop_all(self):
        for w in self.active_workers: w.running = False
        self.active_workers = []
        self.btn_start.configure(state="normal", text=" CHẠY TẤT CẢ")
        self.btn_stop.configure(state="disabled", fg_color="#333")
        self.add_log("!!! ĐANG DỪNG TẤT CẢ CÁC MÁY...")

# --- Login Screen (Activation) ---

class LoginApp(ctk.CTk):
    def __init__(self):
        super().__init__()
        self.title("KÍCH HOẠT Mega-TGHVCT-Tool")
        self.geometry("500x550")
        self.resizable(False, False)
        self.configure(fg_color=BG_COLOR)
        
        self.hwid = get_hwid()
        self.setup_ui()

    def setup_ui(self):
        # Logo & Title
        ctk.CTkLabel(self, text="Mega-TGHVCT-Tool(LD)", font=ctk.CTkFont(size=24, weight="bold"), text_color=ACCENT_GREEN).pack(pady=(40, 10))
        ctk.CTkLabel(self, text="HỆ THỐNG QUẢN LÝ BẢN QUYỀN", font=ctk.CTkFont(size=12)).pack(pady=(0, 30))

        # HWID Box
        hwid_frame = ctk.CTkFrame(self, fg_color=CARD_COLOR, corner_radius=10)
        hwid_frame.pack(padx=40, fill="x")
        ctk.CTkLabel(hwid_frame, text="MÃ MÁY CỦA BẠN (HWID):", font=ctk.CTkFont(size=11, weight="bold")).pack(pady=(10, 0))
        
        # Dùng Entry để dễ copy
        self.hwid_entry = ctk.CTkEntry(hwid_frame, placeholder_text=self.hwid, height=35, font=ctk.CTkFont(size=12))
        self.hwid_entry.insert(0, self.hwid)
        self.hwid_entry.configure(state="readonly")
        self.hwid_entry.pack(padx=20, pady=(5, 10), fill="x")
        
        ctk.CTkLabel(self, text="Hãy gửi mã trên cho Admin để nhận Key kích hoạt.", font=ctk.CTkFont(size=10), text_color="#888").pack(pady=5)

        # Key Input
        self.key_input = ctk.CTkEntry(self, placeholder_text="Nhập Key kích hoạt tại đây...", height=40)
        self.key_input.pack(padx=40, pady=20, fill="x")

        # Buttons
        self.btn_activate = ctk.CTkButton(self, text="KÍCH HOẠT NGAY", command=self.activate, height=45, corner_radius=10, font=ctk.CTkFont(weight="bold"))
        self.btn_activate.pack(padx=40, pady=5, fill="x")
        
        self.status_label = ctk.CTkLabel(self, text="", text_color=ACCENT_RED)
        self.status_label.pack(pady=10)

        # Footer Credit (Nguồn)
        ctk.CTkLabel(self, text="Nguồn: RyoUTE - 0393203161", font=ctk.CTkFont(size=12, weight="bold"), text_color="#777").pack(pady=(30, 20))

    def activate(self):
        key = self.key_input.get().strip()
        if not key:
            self.status_label.configure(text="Vui lòng nhập Key!")
            return
        
        valid, msg = verify_license(key, self.hwid)
        if valid:
            with open(LICENSE_FILE, "w") as f:
                f.write(key)
            self.status_label.configure(text=f"Kích hoạt thành công! Hạn dùng: {msg}", text_color="#4ADE80")
            self.after(1500, self.launch_main)
        else:
            self.status_label.configure(text=msg, text_color=ACCENT_RED)

    def launch_main(self):
        self.destroy()
        main_app = MultiPremiumApp()
        main_app.mainloop()

if __name__ == "__main__":
    # Kiểm tra Key cũ
    hwid = get_hwid()
    need_login = True
    if os.path.exists(LICENSE_FILE):
        with open(LICENSE_FILE, "r") as f:
            saved_key = f.read().strip()
        valid, _ = verify_license(saved_key, hwid)
        if valid:
            need_login = False
    
    if need_login:
        login = LoginApp()
        login.mainloop()
    else:
        app = MultiPremiumApp()
        app.mainloop()
