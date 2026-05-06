import json
import time
import os
import pyperclip
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
SECRET_KEY = "RyoUTE_MegaTGHVCT_Tool_2026"
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

# --- Theme Configuration ---

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
        self.enabled_tasks_vars = None # Sẽ nhận từ UI
        self.log_func = log_func
        self.update_ui_func = update_ui_func
        self.running = False
        # Tasks list: Each task is {name, script, interval, max_runs, current_runs, next_run}
        self.tasks = []
        self.current_task_index = -1
        self.flower_task_active = False
        self.flower_queue = [] # Hàng đợi hoa: tối đa 5 phần tử {flower_info, count, interval}
        self.last_coords = None # Lưu tọa độ click gần nhất để tái sử dụng
        self.status = "Sẵn sàng"
        self.is_lagging = False
        
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

    def get_ld_index(self):
        try:
            # Sửa lỗi: re.search lấy số đầu tiên (ví dụ 127.0.0.1 -> 127) khiến index bị sai
            # Chúng ta sẽ lấy số cuối cùng trong chuỗi serial (thường là port)
            numbers = re.findall(r'\d+', self.device_id)
            if not numbers: return None
            port = int(numbers[-1])
            
            # Nếu port là port ADB chuẩn (5554, 5556...), tính index LDPlayer
            if port >= 5554:
                return (port - 5554) // 2
            return port # Fallback cho các trường hợp đã là index (0, 1, 2...)
        except: return None

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
        
        # Nhật ký chi tiết cho từng bước
        target_desc = ""
        if "target" in step: 
            target_desc = f" -> {os.path.basename(step['target'])}"
        elif "x" in step and "y" in step: 
            target_desc = f" -> ({step['x']}, {step['y']})"
        elif "text" in step: 
            target_desc = f" -> '{step['text']}'"
        elif "timeout" in step and action == "wait":
             target_desc = f" -> {step['timeout']}s"

        self.log(f"BƯỚC: {action}{target_desc}")
        
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
        elif action == "click_coords":
            res = self.click_coords_logic(step)
        elif action == "type_text":
            res = self.type_text_logic(step)
        elif action == "swipe_plant":
            res = self.swipe_plant_logic(step)
        elif action == "wait":
            wait_time = step.get("duration") or step.get("timeout") or 1
            time.sleep(wait_time)
            res = True
        elif action == "click_and_save_coords":
            return self.click_and_save_coords_logic(step)
        elif action == "click_saved_coords":
            res = self.click_saved_coords_logic(step)
        elif action == "log":
            self.log(step.get("text", ""))
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
            idx = self.get_ld_index()
            if idx is None: return False
            
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
                {"action": "click_image", "target1": "images/ngoc_trai.png", "target2": "images/ngoc_trai1.png", "timeout": 10},
                {"action": "click_image_if", "target": "images/thu_hoach.png", "timeout": 3},
                {"action": "wait", "timeout": 2},
                {"action": "click_any", "timeout": 3},
                {"action": "loop_cases",
                    "max_loops": 10,
                    "cases": [
                        {
                            "trigger1": "images/plus.png", "trigger2": "images/plus1.png",
                            "script": [
                                {"action": "click_image", "target1": "images/plus.png" , "target2": "images/plus1.png"},
                                {"action": "click_image_if", "target": "images/the_gioi.png", "timeout": 5},
                                {"action": "click_image", "target": "images/thue.png", "timeout": 10},
                                {"action": "wait", "timeout": 2},
                                {"action": "click_image_if", "target": "images/xac_nhan1.png", "timeout": 5},
                                {"action": "click_image_if", "target": "images/space.png", "timeout": 5},
                            ]
                        }
                    ]
                },
                {"action": "click_image_if", "target1": "images/space1.png", "target2": "images/space.png", "timeout": 5},

            ], 
            interval=60*60*2 + 60*5, # 2 tiếng 5 phút
            max_runs=-1  # -1 là lặp vô tận
        )

        # Task 2: Trồng hoa tươi trong hội
        self.add_task(
            name="Trồng hoa tươi trong hội", 
            script=[
                {"action": "click_image_if", "target": "images/hoi1.png",  "timeout": 20},
                {"action": "click_image_if", "target1": "images/x.png", "target2": "images/x2.png", "timeout": 5},
                {"action": "click_image_if", "target": "images/trong_hoa_tuoi1.png",  "timeout": 20},
                {"action": "click_image_if", "target": "images/tat_ca_thu_hoach.png",  "timeout": 20},
                {"action": "wait", "timeout": 3},
                {"action": "click_image_if", "target": "images/thoat_trong_cay.png",  "timeout": 20},
                {"action": "wait", "timeout": 2},
                {"action": "click_image_if", "target": "images/thoat_hoi1.png",  "timeout": 20},
            ], 
            interval=60*60*2, 
            max_runs=-1
        )
        # Task 3: Mua ở Shop
        self.add_task(
            name="Lấy vàng trong shop", 
            script=[
                {"action": "click_image_if", "target": "images/multi.png",  "timeout": 20},
                {"action": "click_image_if", "target": "images/tiem1.png",  "timeout": 20},
                {"action": "wait", "timeout": 5},
                {"action": "click_image_if", "target": "images/tiem_nguyen_lieu.png",  "timeout": 20},
                {"action": "wait", "timeout": 2},
                {"action": "click_image_if", "target": "images/mua_nhanh.png",  "timeout": 20},
                {"action": "wait", "timeout": 5},
                
                {"action": "click_image_if", "target": "images/xac_nhan1.png",  "timeout": 5},
                {"action": "wait", "timeout": 5},

                {"action": "click_image_if", "target": "images/thoat_tiem.png",  "timeout": 20},
            ], 
            interval=60*60*2 + 60*35, 
            max_runs=-1
        )
        # Task 4: Giao hàng cư dân
        delivery_mode = "item_1_2"
        if self.enabled_tasks_vars and "delivery_mode" in self.enabled_tasks_vars:
            delivery_mode = self.enabled_tasks_vars["delivery_mode"].get()

        if delivery_mode == "all":
            # Kịch bản giao hết (Người dùng sẽ tự làm sau)
            resident_script = [
                {"action": "click_image_if", "target1": "images/nhiem_vu1.jpg","target2": "images/nhiem_vu.jpg","target3": "images/nhiem_vu.png",  "timeout": 5},
                {"action": "click_coords", "x": 325, "y": 550}, 
                {"action": "wait", "timeout": 2},
                {"action": "loop_cases",
                    "max_loops": 8,
                    "cases": [
                        {
                            "trigger": "images/gui.png",
                            "script": [
                                {"action": "click_image", "target": "images/gui.png"},
                                {"action": "wait", "timeout": 2}
                            ]
                        },
                        {
                            "trigger": "images/nhan_mien_phi.png",
                            "script": [
                                {"action": "click_image", "target": "images/nhan_mien_phi.png"},
                                {"action": "wait", "timeout": 2}
                            ]
                        }
                    ]
                },
                {"action": "click_image_if", "target": "images/x1.png",  "timeout": 20},
            ]
        else:
            # Kịch bản hiện tại: Chỉ giao item1, item2
            resident_script = [
                {"action": "click_image_if", "target1": "images/nhiem_vu1.jpg","target2": "images/nhiem_vu.jpg","target3": "images/nhiem_vu.png",  "timeout": 20},
                {"action": "click_coords", "x": 325, "y": 550}, 
                {
                    "action": "if_exists",
                    "target": "images/item1.png",
                    "timeout": 3,
                    "script": [
                        {"action": "click_image", "target": "images/item1.png",  "timeout": 20},
                        {"action": "click_image_if", "target": "images/nhan_nhiem_vu.jpg",  "timeout": 3},
                        {"action": "click_image_if", "target": "images/gui.png",  "timeout": 7},
                        {"action": "wait", "timeout": 2},
                        {
                            "action": "if_exists",
                            "target": "images/muon_xiu_roi_nhan.jpg",
                            "timeout": 3,
                            "script": [
                                {"action": "click_image", "target": "images/muon_xiu_roi_nhan.jpg", "timeout": 20},
                                {"action": "wait", "timeout": 2},
                                {"action": "click_image", "target": "images/xac_nhan1.png", "timeout": 20},
                                {"action": "wait", "timeout": 2},
                                {"action": "click_image", "target": "images/x1.png", "timeout": 20},
                            ]
                        },
                        {
                            "action": "if_exists",
                            "target": "images/x_cu_dan.png",
                            "timeout": 3,
                            "script": [
                                {"action": "click_image", "target": "images/x_cu_dan.png", "timeout": 20},
                            ]
                        },
                    ]
                },
                {
                    "action": "if_exists",
                    "target": "images/item2.png",
                    "timeout": 3,
                    "script": [
                    {"action": "click_image", "target": "images/item2.png",  "timeout": 20},
                    {"action": "click_image_if", "target": "images/nhan_nhiem_vu.jpg",  "timeout": 3},
                    {"action": "click_image_if", "target": "images/gui.png",  "timeout": 7},
                    {"action": "wait", "timeout": 2},
                    {"action": "click_image_if", "target": "images/x1.png",  "timeout": 3},
                    {
                        "action": "if_exists",
                        "target": "images/muon_xiu_roi_nhan.jpg",
                        "timeout": 3,
                        "script": [
                            {"action": "click_image", "target": "images/muon_xiu_roi_nhan.jpg", "timeout": 20},
                            {"action": "wait", "timeout": 2},
                            {"action": "click_image", "target": "images/xac_nhan1.png", "timeout": 20},
                            {"action": "wait", "timeout": 2},
                            {"action": "click_image", "target": "images/x1.png", "timeout": 20},
                        ]
                    },
                    {
                        "action": "if_exists",
                        "target": "images/x_cu_dan.png",
                        "timeout": 3,
                        "script": [
                            {"action": "click_image", "target": "images/x_cu_dan.png", "timeout": 20},
                        ]
                    },
                    ]
                },
                {"action": "click_image", "target": "images/x1.png",  "timeout": 20},
            ]

        self.add_task(
            name="Giao hàng cư dân", 
            script=resident_script, 
            interval=80, 
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
                            "trigger1": "images/do.png","trigger2": "images/do.jpg",
                            "confidence": 0.8,
                            "script": [
                                {"action": "click_image", "target1": "images/do.png","target2": "images/do.jpg", "confidence": 0.8},
                                {"action": "wait", "timeout": 2},
                                {"action": "click_image", "target": "images/chua_co_hang.png"}
                            ]
                        },
                        {
                            "trigger1": "images/vang.png","trigger2": "images/vang1.png", "trigger3": "images/vang2.png","trigger4": "images/vang3.png", "trigger5": "images/vang4.png", "trigger6": "images/vang_con_meo.jpg",
                            "confidence": 0.8,
                            "script": [
                                {"action": "click_image_if", "target1": "images/vang.png","target2": "images/vang1.png", "target3": "images/vang2.png","target4": "images/vang3.png", "target5": "images/vang4.png", "target6": "images/vang_con_meo.jpg", "confidence": 0.8},
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
                                    "target": "images/tiep_tuc.png",
                                    "timeout": 3,
                                    "script": [
                                        {"action": "click_image", "target": "images/tiep_tuc.png"},
                                        {"action": "wait", "timeout": 2},
                                        {"action": "click_image", "target": "images/bo_qua.png"},
                                        {"action": "wait", "timeout": 2},
                                        {"action": "click_any", "timeout": 3},
                                        {"action": "click_image_if", "target": "images/ket_thuc.jpg","timeout": 5},
                                    ]
                                },
                                {
                                    "action": "if_exists",
                                    "target": "images/space1.png",
                                    "timeout": 3,
                                    "script": [
                                        {"action": "click_image", "target": "images/space1.png", "confidence": 0.7},
                                        {"action": "wait", "timeout": 2},
                                        
                                    ]
                                },
                                {
                                    "action": "if_exists",
                                    "target": "images/giai_quyet_van_de.png",
                                    "timeout": 3,
                                    "script": [
                                        {"action": "click_image", "target": "images/giai_quyet_van_de.png", "confidence": 0.8},
                                        {"action": "wait", "timeout": 2},
                                        {"action": "click_image", "target": "images/back.png", "confidence": 0.8},
                                    ]
                                },
                                {
                                    "action": "if_exists",
                                    "target": "images/so_no.png",
                                    "timeout": 3,
                                    "script": [
                                        {"action": "click_image", "target": "images/so_no.png", "confidence": 0.8},
                                        {"action": "wait", "timeout": 2},
                                        {"action": "click_image", "target": "images/back.png", "confidence": 0.8},
                                    ]
                                },
                                {
                                    "action": "if_exists",
                                    "target": "images/meo_ngoan.png",
                                    "timeout": 3,
                                    "script": [
                                        {"action": "click_image", "target": "images/meo_ngoan.png", "confidence": 0.8},
                                        {"action": "wait", "timeout": 2},
                                        {"action": "click_image", "target": "images/back.png", "confidence": 0.8},
                                    ]
                                }
                            ]
                        },
                        {
                            "trigger1": "images/xanh.png", "trigger2": "images/xanh2.png",
                            "confidence": 0.8,
                            "script": [
                                {"action": "click_image", "target1": "images/xanh.png", "target2": "images/xanh2.png", "confidence": 0.8},
                                {"action": "click_image", "target": "images/giao.png"},
                                {"action": "click_any", "timeout": 3},
                                {
                                    "action": "if_exists",
                                    "target": "images/next.png",
                                    "timeout": 3,
                                    "script": [
                                        {"action": "click_image", "target": "images/xanh.png"},
                                        {"action": "wait", "timeout": 2},
                                        {"action": "click_image", "target": "images/nhan.png"},
                                        {"action": "click_image", "target": "images/xx.png"},
                                    ]
                                },
                                {
                                    "action": "if_exists",
                                    "target": "images/nhan_nuoc.png",
                                    "timeout": 3,
                                    "script": [
                                        {"action": "click_image_if", "target": "images/nhan_nuoc.png", "timeout": 5},
                                        {"action": "click_any", "timeout": 3},
                                        {"action": "click_image", "target": "images/x4.png"},
                                    ]
                                },
                            ]
                        }
                    ]
                }
            ], 
            interval=30, 
            max_runs=-1
        )
        # Task 6: Trưng bày hoa
        self.add_task(
            name="Trưng bày hoa", 
            script=[
                {"action": "click_image_if", "target": "images/lay_tien.png",  "timeout": 7},
                {"action": "click_image_if", "target": "images/lay_tien.png",  "timeout": 7},
                {"action": "click_image_if", "target": "images/lay_tien.png",  "timeout": 7},
                {"action": "click_image", "target": "images/trung_bay_hoa.png", "target1": "images/trung_bay_hoa1.jpg",  "timeout": 20},
                {"action": "wait", "timeout": 3},
                {"action": "click_coords", "x": 100, "y": 740}, 
                {"action": "click_image_if", "target": "images/bay_ban.png",  "timeout": 10},
                {"action": "wait", "timeout": 3},
                {"action": "click_coords", "x": 100, "y": 740}, 
                {"action": "click_image_if", "target": "images/bay_ban.png",  "timeout": 10},
                {"action": "wait", "timeout": 3},
                {"action": "click_coords", "x": 100, "y": 740}, 
                {"action": "click_image_if", "target": "images/bay_ban.png",  "timeout": 10},
                {"action": "wait", "timeout": 3},
                {"action": "click_coords", "x": 100, "y": 740}, 
                {"action": "click_image_if", "target": "images/bay_ban.png",  "timeout": 10},
                {"action": "wait", "timeout": 5},
                {"action": "click_coords", "x": 100, "y": 740}, 
                {"action": "click_image_if", "target": "images/bay_ban.png",  "timeout": 10},
                {"action": "wait", "timeout": 3},
                {"action": "click_coords", "x": 100, "y": 740}, 
                {"action": "click_image_if", "target": "images/bay_ban.png",  "timeout": 10},
                {"action": "click_image", "target": "images/space1.png",  "timeout": 20},
            ], 
            interval=60*55, 
            max_runs=-1
        )


    def loop_cases_logic(self, step):
        cases = step.get("cases", [])
        if not cases: return True
        
        timeout = step.get("timeout", 10)
        max_loops = step.get("max_loops", -1)  # -1 = không giới hạn
        
        log_msg = f"BẮT ĐẦU VÒNG LẶP SỰ KIỆN: Chờ tối đa {timeout}s"
        if max_loops != -1:
            log_msg += f", tối đa {max_loops} lần khớp"
        self.log(log_msg + "...")
        
        start_loop_time = time.time()
        iteration = 0
        loops_matched = 0  # Đếm số lần đã khớp và thực thi thành công
        
        while self.running:
            iteration += 1
            
            # Kiểm tra giới hạn số lần lặp
            if max_loops != -1 and loops_matched >= max_loops:
                self.log(f"-> KẾT THÚC VÒNG LẶP: Đã đạt giới hạn {max_loops} lần.")
                break
            
            found_any = False
            screen = self.get_screenshot()
            
            if screen is None: 
                time.sleep(1)
                continue
            
            best_overall_match = 0
            best_overall_name = ""
            
            for case in cases:
                # Thu thập tất cả triggers (trigger, trigger1, trigger2...)
                triggers = []
                if case.get("trigger"): triggers.append(case.get("trigger"))
                idx = 1
                while f"trigger{idx}" in case:
                    triggers.append(case.get(f"trigger{idx}"))
                    idx += 1
                
                sub_script = case.get("script", [])
                confidence = case.get("confidence", 0.8)
                
                case_matched = False
                for t_path in triggers:
                    t_img = get_cached_image(t_path)
                    if t_img is None: continue
                    
                    try:
                        res = cv2.matchTemplate(screen, t_img, cv2.TM_CCOEFF_NORMED)
                        _, max_val, _, _ = cv2.minMaxLoc(res)
                        del res
                        
                        if max_val > best_overall_match:
                            best_overall_match = max_val
                            best_overall_name = os.path.basename(t_path)
                        
                        if max_val >= confidence:
                            self.log(f"-> PHÁT HIỆN BIẾN CỐ: {os.path.basename(t_path)} (Khớp: {max_val:.2f}/{confidence})")
                            case_matched = True
                            found_any = True
                            break # Thoát vòng lặp triggers để thực hiện script
                    except: continue
                
                if case_matched:
                    step_failed = False
                    for s_step in sub_script:
                        if not self.running: break
                        if not self.execute_step(s_step):
                            step_failed = True
                            break
                    if step_failed:
                        self.log("-> DỪNG VÒNG LẶP: Một bước trong kịch bản con bị lỗi.")
                        return True
                    loops_matched += 1  # Tăng bộ đếm mỗi lần khớp
                    break # Thoát vòng lặp cases để chụp ảnh màn hình mới
            
            del screen
            
            if found_any:
                start_loop_time = time.time() 
                time.sleep(0.5)
                continue
            else:
                elapsed = time.time() - start_loop_time
                if elapsed >= timeout:
                    if best_overall_match > 0.4:
                        self.log(f"-> KẾT THÚC VÒNG LẶP: Hết thời gian (Tốt nhất: {best_overall_name} {best_overall_match:.2f})")
                    break
                time.sleep(1)
            
        return True

    def if_exists_logic(self, step):
        targets = []
        if step.get("target"): targets.append(step.get("target"))
        idx = 1
        while f"target{idx}" in step:
            targets.append(step.get(f"target{idx}"))
            idx += 1
            
        sub_script = step.get("script", [])
        timeout = step.get("timeout", 0)
        if not targets: return True
        
        target_names = [os.path.basename(t) for t in targets]
        self.log(f"Đang kiểm tra (if_exists): {', '.join(target_names)} (Chờ tối đa {timeout}s)")
        
        start_time = time.time()
        found = False
        confidence = step.get("confidence", 0.8)
        last_log_time = start_time
        
        while time.time() - start_time <= timeout or (timeout == 0 and found == False):
            screen = self.get_screenshot()
            if screen is not None:
                best_match = 0
                for t_path in targets:
                    t_img = get_cached_image(t_path)
                    if t_img is None: continue
                    try:
                        res = cv2.matchTemplate(screen, t_img, cv2.TM_CCOEFF_NORMED)
                        _, max_val, _, _ = cv2.minMaxLoc(res)
                        del res
                        if max_val > best_match: best_match = max_val
                        if max_val >= confidence:
                            found = True
                            break
                    except: continue
                
                if found:
                    del screen
                    break
                    
                cur_time = time.time()
                if cur_time - last_log_time >= 2:
                    if best_match > 0.4:
                        self.log(f"   [if_exists] Chưa khớp (Max: {best_match:.2f}/{confidence})")
                    last_log_time = cur_time
                del screen
            if timeout == 0: break
            time.sleep(0.5)
            
        if found:
            self.log(f"-> ĐIỀU KIỆN ĐÚNG: Thực hiện kịch bản con...")
            for s_step in sub_script:
                if not self.running: break
                self.execute_step(s_step)
        return True

    def click_any_logic(self, step):
        delay = step.get("timeout", 0)
        if delay > 0:
            self.log(f"HỆ THỐNG: Chờ {delay}s trước khi click...")
            time.sleep(delay)
        
        screen = self.get_screenshot()
        if screen is not None:
            h, w = screen.shape[:2]
            cx, cy = w // 2, h // 3
            self.call_adb(["shell", "input", "tap", str(cx), str(cy)])
            self.log(f"CLICK ANY: Toạ độ ({cx}, {cy})")
            del screen
            return True
        return False

    def type_text_logic(self, step):
        text = str(step.get("text", "")).strip()
        if not text: return True
        
        self.log(f"TIẾN TRÌNH NHẬP: '{text}' (Tránh xung đột Clipboard)")
        
        # 1. Xóa nội dung cũ trong textbox
        for _ in range(20):
            self.call_adb(["shell", "input", "keyevent", "67"]) # Phím Backspace
        time.sleep(0.2)
        
        # 2. Lấy đường dẫn ldconsole
        idx = self.get_ld_index()
        ld_console = self.ld_path
        if ld_console and os.path.isdir(ld_console):
            ld_console = os.path.join(ld_console, "ldconsole.exe")
        elif ld_console and not ld_console.lower().endswith("ldconsole.exe"):
            ld_dir = os.path.dirname(ld_console)
            ld_console = os.path.join(ld_dir, "ldconsole.exe")

        success = False
        if idx is not None and os.path.exists(ld_console):
            # Thử gõ ngang bằng lệnh của LDPlayer (Bắn text thẳng vào vùng đang focus, không dùng Windows Clipboard)
            cmd = [ld_console, "action", "--index", str(idx), "--key", "call.input", "--value", text]
            try:
                subprocess.run(cmd, creationflags=subprocess.CREATE_NO_WINDOW)
                success = True
            except:
                pass
                
        # 3. Dự phòng: Dùng ADB thuần túy nếu ldconsole thất bại
        if not success:
            escaped_text = self.escape_adb_text(text)
            self.call_adb(["shell", "input", "text", escaped_text])
            
        time.sleep(0.5)
        return True

    def click_saved_coords_logic(self, step):
        if self.last_coords:
            cx, cy = self.last_coords
            # Thêm một chút độ trễ nếu có yêu cầu
            wait_time = step.get("wait_before", 0)
            if wait_time > 0: time.sleep(wait_time)
            
            self.call_adb(["shell", "input", "tap", str(cx), str(cy)])
            self.log(f"CLICK TỌA ĐỘ LƯU: ({cx}, {cy})")
            return True
        else:
            self.log("LỖI: Chưa có tọa độ được lưu để click!")
            return False

    def click_coords_logic(self, step):
        x = step.get("x")
        y = step.get("y")
        if x is not None and y is not None:
            delay = step.get("timeout", 0)
            if delay > 0: time.sleep(delay)
            self.call_adb(["shell", "input", "tap", str(x), str(y)])
            self.log(f"CLICK TỌA ĐỘ: ({x}, {y})")
            return True
        return False

    def swipe_plant_logic(self, step):
        self.log("BẮT ĐẦU TRỒNG TAY (Lia qua các ô)...")
        sx = step.get("x", 80)
        sy = step.get("y", 590)
        
        screen = self.get_screenshot()
        if screen is None:
            w, h = 1280, 720
        else:
            h, w = screen.shape[:2]
            del screen
            
        y_start = int(h * 0.15)
        y_end = int(h * 0.75)
        y_step = int(h * 0.15)
        
        x_points = [int(w * 0.2), int(w * 0.5), int(w * 0.8)]
        
        for y in range(y_start, y_end, y_step):
            for x in x_points:
                if not self.running: break
                self.call_adb(["shell", "input", "swipe", str(sx), str(sy), str(x), str(y), "600"])
                time.sleep(0.1)
                
        self.log("HOÀN TẤT LIA TRỒNG TAY.")
        return True

    def click_image_logic(self, step):
        targets = []
        if step.get("target"): targets.append(step.get("target"))
        i = 1
        while f"target{i}" in step:
            targets.append(step.get(f"target{i}"))
            i += 1
        
        timeout = step.get("timeout", 10)
        confidence = step.get("confidence", 0.8)
        
        prepared_targets = []
        for t_path in targets:
            t_img = get_cached_image(t_path, grayscale=False)
            if t_img is not None:
                prepared_targets.append((t_path, t_img))
            else:
                self.log(f"LỖI FILE: Không phân tích được ảnh: {t_path}")

        if not prepared_targets:
            return False

        target_names = [os.path.basename(t[0]) for t in prepared_targets]
        self.log(f"Đang đợi xuất hiện để click: {', '.join(target_names)} (Timeout: {timeout}s)")

        start = time.time()
        last_log_time = start
        
        while time.time() - start < timeout and self.running:
            screen = self.get_screenshot()
            if screen is not None:
                best_match = 0
                best_img_name = ""
                
                for t_path, t_img in prepared_targets:
                    res = cv2.matchTemplate(screen, t_img, cv2.TM_CCOEFF_NORMED)
                    _, max_val, _, max_loc = cv2.minMaxLoc(res)
                    del res
                    
                    if max_val > best_match:
                        best_match = max_val
                        best_img_name = os.path.basename(t_path)
                    
                    if max_val >= confidence:
                        th, tw = t_img.shape[:2]
                        cx, cy = max_loc[0] + tw//2, max_loc[1] + th//2
                        if "click_image_if" not in step.get("action", "") or best_match > 0:
                            self.call_adb(["shell", "input", "tap", str(cx), str(cy)])
                        self.log(f"-> CLICK THÀNH CÔNG: {os.path.basename(t_path)} [Tọa độ: {cx},{cy}] (Khớp: {max_val:.2f}/{confidence})")
                        del screen
                        return True
                del screen 
                
                cur_time = time.time()
                if cur_time - last_log_time >= 2.0:
                    if best_match > 0.4:
                        self.log(f"   [Quét ảnh] Chưa khớp. Tốt nhất hiện tại: {best_img_name} ({best_match:.2f}/{confidence})")
                    last_log_time = cur_time
                    
            time.sleep(1)
            
        self.log(f"-> CLICK THẤT BẠI: Đã chờ {timeout}s nhưng không có ảnh nào đạt độ khớp {confidence}.")
        return False

    def click_and_save_coords_logic(self, step):
        targets = []
        if step.get("target"): targets.append(step.get("target"))
        
        timeout = step.get("timeout", 10)
        confidence = step.get("confidence", 0.8)
        
        prepared_targets = []
        for t_path in targets:
            t_img = get_cached_image(t_path, grayscale=False)
            if t_img is not None:
                prepared_targets.append((t_path, t_img))

        if not prepared_targets:
            return False

        target_names = [os.path.basename(t[0]) for t in prepared_targets]
        self.log(f"Đang đợi click và lưu tọa độ (Vùng giữa): {', '.join(target_names)} (Timeout: {timeout}s)")

        start = time.time()
        last_log_time = start
        
        while time.time() - start < timeout and self.running:
            screen = self.get_screenshot()
            if screen is not None:
                h, w = screen.shape[:2]
                
                # CHỈ QUÉT VÙNG GIỮA (Loại bỏ 20% mỗi bên trái/phải, 15% trên/dưới)
                # Giúp tránh nhận diện nhầm các icon ở rìa màn hình (sidebar/header/footer)
                x1, x2 = int(w * 0.20), int(w * 0.80)
                y1, y2 = int(h * 0.15), int(h * 0.85)
                roi = screen[y1:y2, x1:x2]
                
                best_match = 0
                best_img_name = ""
                
                for t_path, t_img in prepared_targets:
                    # Đảm bảo ảnh mẫu nhỏ hơn vùng quét
                    th, tw = t_img.shape[:2]
                    if th > (y2-y1) or tw > (x2-x1): continue

                    res = cv2.matchTemplate(roi, t_img, cv2.TM_CCOEFF_NORMED)
                    _, max_val, _, max_loc = cv2.minMaxLoc(res)
                    del res
                    
                    if max_val > best_match:
                        best_match = max_val
                        best_img_name = os.path.basename(t_path)
                        
                    if max_val >= confidence:
                        # Tọa độ thực tế = Tọa độ trong ROI + Tọa độ gốc của ROI
                        cx, cy = max_loc[0] + x1 + tw//2, max_loc[1] + y1 + th//2
                        
                        # PHẦN QUAN TRỌNG: Lưu tọa độ để dùng cho sau này (tưới cây/thu hoạch)
                        self.last_coords = (cx, cy)
                        self.call_adb(["shell", "input", "tap", str(cx), str(cy)])
                        self.log(f"-> CLICK & LƯU TỌA ĐỘ: {os.path.basename(t_path)} -> ({cx}, {cy}) (Khớp: {max_val:.2f})")
                        del screen
                        return True
                del screen 
                
                cur_time = time.time()
                if cur_time - last_log_time >= 2.0:
                    if best_match > 0.4:
                        self.log(f"   [Quét lưu tọa độ] Chưa khớp ở vùng giữa. Tốt nhất: {best_img_name} ({best_match:.2f}/{confidence})")
                    last_log_time = cur_time
                    
            time.sleep(1)
            
        self.log(f"-> THẤT BẠI: Hết {timeout}s không khớp ảnh nào trong vùng giữa để lưu tọa độ.")
        return False

    def add_task(self, name, script, interval=60, max_runs=-1, initial_delay=0):
        self.tasks.append({
            "name": name,
            "script": script,
            "interval": interval,
            "max_runs": max_runs,
            "current_runs": 0,
            "next_run": time.time() + initial_delay
        })

    def add_flower_task(self, flower_info, harvest_count=1, harvest_interval=60):
        if len(self.flower_queue) >= 50:
            self.log(f"CẢNH BÁO: Hàng đợi hoa đã đầy (50/50). Không thể thêm {flower_info['name']}.")
            return
            
        self.flower_queue.append({
            "flower_info": flower_info,
            "harvest_count": harvest_count,
            "harvest_interval": harvest_interval
        })
        self.log(f"ĐÃ THÊM HÀNG ĐỢI: {flower_info['name']} ({len(self.flower_queue)}/50)")
        
        # Nếu chưa có task trồng hoa nào đang chạy thì kích hoạt hoa đầu tiên
        has_flower_task = any(t.get("name") in ["Flower_Plant", "Flower_Harvest"] for t in self.tasks)
        if not has_flower_task:
            self.schedule_next_flower()

    def schedule_next_flower(self):
        if not self.flower_queue:
            self.flower_task_active = False
            return
            
        next_item = self.flower_queue[0]
        f = next_item["flower_info"]
        
        # Sử dụng f["name"] làm search text
        search_txt = f["name"][:20] 
        trong_tay = f.get("trong_tay", False)
        
        # --- GIAI ĐOẠN 1: TRỒNG VÀ TƯỚI NƯỚC (Chạy nhanh, không đợi) ---
        if trong_tay:
            script_plant = [
                {"action": "click_and_save_coords", "target": "images/dat_trong.png", "timeout": 20},
                {"action": "wait", "timeout": 3},
                {"action": "click_coords", "x": 200, "y": 520}, # Click ô tìm kiếm
                {"action": "wait", "timeout": 3},
                {"action": "type_text", "text": search_txt},
                {"action": "wait", "timeout": 3},
                {"action": "swipe_plant", "x": 80, "y": 590},
                {"action": "wait", "timeout": 5},
                {"action": "click_coords", "x": 500, "y": 100}, # Thoát menu nếu cần
                {"action": "wait", "timeout": 2},
                {"action": "click_saved_coords"}, # Nhấn vào đất để hiện menu/tưới
                {"action": "click_saved_coords"},
                {"action": "click_image", "target": "images/tuoi_nhanh.png", "timeout": 20}
            ]
        else:
            script_plant = [
                {"action": "click_and_save_coords", "target": "images/dat_trong.png", "timeout": 20},
                {"action": "click_image_if", "target": "images/trong_nhanh.png", "timeout": 5},
                {"action": "click_image_if", "target": "images/trong_nhanh.png", "timeout": 5},
                {"action": "wait", "timeout": 3},
                {"action": "click_coords", "x": 200, "y": 520}, # Click ô tìm kiếm
                {"action": "wait", "timeout": 3},
                {"action": "type_text", "text": search_txt},
                {"action": "wait", "timeout": 3},
                {"action": "click_coords", "x": 80, "y": 590},
                {"action": "click_coords", "x": 80, "y": 590}, # Click chọn hoa đầu tiên
                {"action": "wait", "timeout": 5},
                {"action": "click_saved_coords"}, # Nhấn vào đất để hiện menu/tưới
                {"action": "click_saved_coords"},
                {"action": "click_image", "target": "images/tuoi_nhanh.png", "timeout": 20}
            ]
        
        # Thêm task trồng, chạy xong task này sẽ chuyển sang phase thu hoạch
        self.add_task("Flower_Plant", script_plant, interval=0, max_runs=1)
        self.flower_task_active = True
        self.log(f"TIẾN HÀNH TRỒNG: {f['name']}")

    def schedule_harvest(self, is_first=True):
        if not self.flower_queue: return
        
        next_item = self.flower_queue[0]
        f = next_item["flower_info"]
        inter = next_item["harvest_interval"]
        growth = f.get("growth_time", 30)
        cham_nhanh = f.get("cham_nhanh", False)
        
        if cham_nhanh and not is_first:
            script_harvest = [
                {"action": "wait", "timeout": 2},
                {"action": "click_saved_coords"},
                {"action": "click_saved_coords"},
                {"action": "click_image_if", "target": "images/tang_toc_nhanh.jpg", "timeout": 5},
                {"action": "wait", "timeout": 3},
                {"action": "click_saved_coords"},
                {"action": "click_saved_coords"},
                {"action": "click_image_if", "target": "images/thu_hoach_nhanh.png", "timeout": 5}
            ]
            delay = 0
        else:
            # Kịch bản cho 1 lần thu hoạch
            script_harvest = [
                {"action": "wait", "timeout": 5},
                {"action": "click_saved_coords"},
                {"action": "click_saved_coords"},
                {"action": "click_image_if", "target": "images/thu_hoach_nhanh.png", "timeout": 5}
            ]
            # Lần đầu (sau khi tưới xong) thu hoạch ngay lập tức, các lần sau chờ thời gian giữa các đợt (inter)
            delay = 0 if is_first else inter
        
        # Thêm task thu hoạch chạy 1 lần sau thời gian delay (giúp xen kẽ task khác)
        self.add_task("Flower_Harvest", script_harvest, interval=0, max_runs=1, initial_delay=delay)
        self.log(f"ĐÃ LÊN LỊCH THU HOẠCH: {f['name']} sau {delay}s")

    def stop_flower_task(self):
        new_tasks = []
        for t in self.tasks:
            if t.get("name") not in ["Flower_Plant", "Flower_Harvest"]:
                new_tasks.append(t)
        self.tasks = new_tasks
        self.flower_queue = [] 
        self.flower_task_active = False
        self.log("Đã dừng và xóa sạch hàng đợi trồng hoa.")

    def run(self):
        self.running = True
        self.log(f"HỆ THỐNG: Bất đầu trình quản lý đa tác vụ ({len(self.tasks)} tác vụ).")
        
        while self.running:
            now = time.time()
            # 1. Tìm tất cả các tác vụ đang đến hạn (hoặc quá hạn)
            due_tasks = []
            next_task_time = float('inf')
            
            for task in self.tasks[:]:
                # Kiểm tra xem Task này có đang được bật trên UI không
                t_name = task.get("name")
                if self.enabled_tasks_vars:
                    if t_name in ["Flower_Plant", "Flower_Harvest"]:
                        if not self.enabled_tasks_vars.get("Trồng hoa tự động").get():
                            continue
                    elif t_name in self.enabled_tasks_vars:
                        if not self.enabled_tasks_vars.get(t_name).get():
                            continue

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
                    
                    # Logic chuyển tiếp cho Flower Task (Tránh làm nghẽn các task khác)
                    if task.get("name") == "Flower_Plant":
                        # Trồng xong -> Chuyển sang giai đoạn chờ thu hoạch lượt đầu
                        self.schedule_harvest(is_first=True)
                        
                    elif task.get("name") == "Flower_Harvest":
                        if self.flower_queue:
                            next_item = self.flower_queue[0]
                            next_item["harvest_count"] -= 1
                            
                            if next_item["harvest_count"] > 0:
                                # Nếu vẫn còn lượt thu hoạch, lên lịch thu hoạch tiếp theo sau 'inter' giây
                                self.schedule_harvest(is_first=False)
                            else:
                                # Đã thu hoạch xong hết tất cả các lượt
                                self.flower_queue.pop(0)
                                self.schedule_next_flower()
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
                if next_task_time == float('inf'):
                    self.update_status("Đang chờ lệnh...")
                else:
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
        self.title("Tool Mr Thanh - Thế Giới Hoa Viên")
        self.geometry("1100x780")
        self.configure(fg_color=BG_COLOR)
        
        self.active_workers = [] # Các thread đang chạy
        self.instances = [] # Danh sách các máy thực tế đang chạy ADB
        self.adb_path = self.find_adb()
        self.ld_path = r"C:\LDPlayer\LDPlayer9\ldconsole.exe" # Mặc định
        
        self.flower_queue = [] # Danh sách tối đa 5 hoa đang đợi trồng

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
        
        ctk.CTkLabel(self.sidebar, image=self.logo_img, text="").pack(pady=(20,0))
        self.logo_label = ctk.CTkLabel(self.sidebar, text="BẢNG ĐIỀU KHIỂN", font=ctk.CTkFont(size=20, weight="bold"), text_color=ACCENT_GREEN)
        self.logo_label.pack(pady=(10, 0))
        ctk.CTkLabel(self.sidebar, text="Tool Mr Thanh - Thế Giới Hoa Viên", font=ctk.CTkFont(size=11)).pack(pady=(0, 15))

        # LDPlayer Path Config
        self.path_card = ctk.CTkFrame(self.sidebar, fg_color=CARD_COLOR, corner_radius=10)
        self.path_card.pack(padx=20, pady=5, fill="x")
        ctk.CTkLabel(self.path_card, text="ĐƯỜNG DẪN LDPLAYER", font=ctk.CTkFont(size=10, weight="bold")).pack(pady=(5, 0))
        self.ld_path_entry = ctk.CTkEntry(self.path_card, placeholder_text="Ví dụ: C:\LDPlayer\LDPlayer9", height=28)
        self.ld_path_entry.pack(padx=10, pady=5, fill="x")
        self.ld_path_entry.insert(0, r"C:\LDPlayer\LDPlayer9")
        
        self.save_button = ctk.CTkButton(self.path_card, text="Lưu Cấu Hình", command=self.save_config, height=28)
        self.save_button.pack(padx=10, pady=10, fill="x")


        # Control
        self.btn_start = ctk.CTkButton(self.sidebar, text=" CHẠY TẤT CẢ", image=self.start_icon, compound="left", command=self.start_all, height=38, corner_radius=10, font=ctk.CTkFont(size=14, weight="bold"))
        self.btn_start.pack(padx=20, pady=(20, 8), fill="x")
        self.btn_stop = ctk.CTkButton(self.sidebar, text=" DỪNG TẤT CẢ", image=self.stop_icon, compound="left", command=self.stop_all, fg_color="#333", height=38, corner_radius=10)
        self.btn_stop.pack(padx=20, pady=8, fill="x")

        # Task Management (QUẢN LÝ TÁC VỤ)
        self.task_frame = ctk.CTkFrame(self.sidebar, fg_color=CARD_COLOR, corner_radius=10)
        self.task_frame.pack(padx=20, pady=10, fill="x")
        ctk.CTkLabel(self.task_frame, text="QUẢN LÝ TÁC VỤ", font=ctk.CTkFont(size=11, weight="bold"), text_color=ACCENT_GREEN).pack(pady=(5, 5))
        
        self.enabled_tasks = {
            "Thuê Ngọc Trai": ctk.BooleanVar(value=True),
            "Trồng hoa tươi trong hội": ctk.BooleanVar(value=True),
            "Lấy vàng trong shop": ctk.BooleanVar(value=True),
            "Giao hàng cư dân": ctk.BooleanVar(value=True),
            "Giao hàng tại sảnh": ctk.BooleanVar(value=True),
            "Trưng bày hoa": ctk.BooleanVar(value=True),
            "Trồng hoa tự động": ctk.BooleanVar(value=True),
        }
        
        for task_name, var in self.enabled_tasks.items():
            cb = ctk.CTkCheckBox(self.task_frame, text=task_name, variable=var, font=ctk.CTkFont(size=11), checkbox_width=18, checkbox_height=18)
            cb.pack(padx=10, pady=2, anchor="w")
            
            if task_name == "Giao hàng cư dân":
                self.delivery_mode_var = ctk.StringVar(value="item_1_2")
                mode_frame = ctk.CTkFrame(self.task_frame, fg_color="transparent")
                mode_frame.pack(padx=(30, 0), pady=(0, 5), anchor="w")
                
                rb1 = ctk.CTkRadioButton(mode_frame, text="Item 1, 2", variable=self.delivery_mode_var, value="item_1_2", font=ctk.CTkFont(size=10), radiobutton_width=14, radiobutton_height=14)
                rb1.pack(side="left", padx=(0, 10))
                
                rb2 = ctk.CTkRadioButton(mode_frame, text="Giao hết", variable=self.delivery_mode_var, value="all", font=ctk.CTkFont(size=10), radiobutton_width=14, radiobutton_height=14)
                rb2.pack(side="left")

        self.enabled_tasks["delivery_mode"] = self.delivery_mode_var

    
        # 2. Main Area
        self.main_content = ctk.CTkFrame(self, fg_color="transparent")
        self.main_content.pack(side="right", fill="both", expand=True, padx=20, pady=(5, 20))

        # Instance Selection Card
        self.inst_frame = ctk.CTkFrame(self.main_content, fg_color=CARD_COLOR, corner_radius=15, border_width=1, border_color="#333")
        self.inst_frame.pack(fill="x", pady=(0, 2))
        inst_header = ctk.CTkFrame(self.inst_frame, fg_color="transparent")
        inst_header.pack(fill="x", padx=15, pady=1)
        ctk.CTkLabel(inst_header, text="THIẾT BỊ ĐANG MỞ", font=ctk.CTkFont(size=11, weight="bold"), text_color=ACCENT_GREEN).pack(side="left")

        # Action Buttons for Instances
        btns_frame = ctk.CTkFrame(inst_header, fg_color="transparent")
        btns_frame.pack(side="right")
        # Nút chọn tất cả được gỡ bỏ vì người dùng muốn chạy tất cả máy mà không cần check
        self.btn_refresh = ctk.CTkButton(btns_frame, text="Làm Mới Danh Sách", command=self.scan_devices, height=22, width=110, font=ctk.CTkFont(size=10, weight="bold"))
        self.btn_refresh.pack(side="left", padx=5)

        self.device_list_frame = ctk.CTkScrollableFrame(self.inst_frame, height=40, fg_color="transparent") 
        self.device_list_frame.pack(fill="x", padx=10, pady=(0, 2))
        # Tăng số cột lên 12 và cấu hình cột đều nhau
        for col in range(12): 
            self.device_list_frame.grid_columnconfigure(col, weight=1)
        self.device_cards = {}


        # View Area
        self.view_card = ctk.CTkFrame(self.main_content, fg_color=CARD_COLOR, corner_radius=15)
        self.view_card.pack(fill="both", expand=True)
        
        # Thay thế TabView bằng Frame trực tiếp để hiển thị Cấu hình trồng hoa
        self.tab_flower = ctk.CTkFrame(self.view_card, fg_color="transparent")
        self.tab_flower.pack(fill="both", expand=True, padx=5, pady=5)

        # Flower UI Setup
        self.setup_flower_ui()

    def setup_flower_ui(self):
        # 1. Khu vực hiển thị Hoa đang trồng (ACTIVE STATUS)
        self.active_flower_card = ctk.CTkFrame(self.tab_flower, fg_color="#1A1A1A", corner_radius=15, border_width=1, border_color=ACCENT_GREEN)
        self.active_flower_card.pack(fill="x", padx=20, pady=(10, 5))
        
        # Tạo sẵn cấu trúc tĩnh để tránh rebuild gây giật
        self.flower_header = ctk.CTkFrame(self.active_flower_card, fg_color="transparent")
        self.flower_header.pack(fill="x", padx=15, pady=(10, 5))
        self.lbl_queue_count = ctk.CTkLabel(self.flower_header, text="HÀNG ĐỢI TRỒNG HOA (0/50)", font=ctk.CTkFont(size=13, weight="bold"), text_color=ACCENT_GREEN)
        self.lbl_queue_count.pack(side="left")
        ctk.CTkButton(self.flower_header, text=" DỪNG TẤT CẢ ", command=self.stop_flower_planting_all, fg_color=ACCENT_RED, width=120, height=28, font=ctk.CTkFont(size=11, weight="bold")).pack(side="right")

        self.flower_scroll = ctk.CTkScrollableFrame(self.active_flower_card, fg_color="transparent", height=160)
        self.flower_scroll.pack(fill="both", expand=True, padx=5, pady=(0, 5))
        
        self.flower_ui_items = []
        self._last_queue_key = ""
        
        # 2. Khu vực Form nhập liệu (Manual Input)
        self.input_card = ctk.CTkFrame(self.tab_flower, fg_color=CARD_COLOR, corner_radius=15, border_width=1, border_color="#333")
        self.input_card.pack(fill="x", padx=20, pady=5)
        
        header = ctk.CTkFrame(self.input_card, fg_color="transparent")
        header.pack(fill="x", padx=20, pady=(15, 10))
        ctk.CTkLabel(header, text="THÊM HOA VÀO HÀNG ĐỢI", font=ctk.CTkFont(size=14, weight="bold"), text_color=ACCENT_GREEN).pack(side="left")

        # Form fields
        form_frame = ctk.CTkFrame(self.input_card, fg_color="transparent")
        form_frame.pack(fill="x", padx=20, pady=(0, 10))
        
        # Cột 1: Tên hoa
        col1 = ctk.CTkFrame(form_frame, fg_color="transparent")
        col1.pack(side="left", fill="both", expand=True, padx=(0, 10))
        ctk.CTkLabel(col1, text="Tên hoa cần tìm:", font=ctk.CTkFont(size=11)).pack(anchor="w")
        self.ent_flower_name = ctk.CTkEntry(col1, placeholder_text="Ví dụ: Sơn Trà...", height=35)
        self.ent_flower_name.pack(fill="x", pady=(5, 0))
        
        # Cột 2: Số lần thu
        col2 = ctk.CTkFrame(form_frame, fg_color="transparent")
        col2.pack(side="left", padx=10)
        ctk.CTkLabel(col2, text="Số lần thu hoạch:", font=ctk.CTkFont(size=11)).pack(anchor="w")
        self.ent_harvest_count = ctk.CTkEntry(col2, width=90, height=35)
        self.ent_harvest_count.pack(pady=(5, 0))
        self.ent_harvest_count.insert(0, "1")
        
        # Cột 3: Giãn cách
        col3 = ctk.CTkFrame(form_frame, fg_color="transparent")
        col3.pack(side="left", padx=10)
        ctk.CTkLabel(col3, text="Giãn cách(s):", font=ctk.CTkFont(size=11)).pack(anchor="w")
        self.ent_harvest_interval = ctk.CTkEntry(col3, width=90, height=35)
        self.ent_harvest_interval.pack(pady=(5, 0))
        self.ent_harvest_interval.insert(0, "60")
        
        # Cột 4: Switches (Chăm nhanh, Trồng tay)
        col4 = ctk.CTkFrame(form_frame, fg_color="transparent")
        col4.pack(side="left", padx=10)
        
        self.var_cham_nhanh = ctk.BooleanVar(value=False)
        self.var_trong_tay = ctk.BooleanVar(value=False)
        
        cb_cham_nhanh = ctk.CTkCheckBox(col4, text="Chăm nhanh", variable=self.var_cham_nhanh, font=ctk.CTkFont(size=11), checkbox_width=18, checkbox_height=18)
        cb_cham_nhanh.pack(anchor="w", pady=(5, 2))
        
        cb_trong_tay = ctk.CTkCheckBox(col4, text="Trồng tay", variable=self.var_trong_tay, font=ctk.CTkFont(size=11), checkbox_width=18, checkbox_height=18)
        cb_trong_tay.pack(anchor="w")

        # Nút THÊM (Cột 5)
        col5 = ctk.CTkFrame(form_frame, fg_color="transparent")
        col5.pack(side="right", padx=(10, 0))
        ctk.CTkLabel(col5, text="", font=ctk.CTkFont(size=11)).pack(anchor="w")
        self.btn_add_manual = ctk.CTkButton(col5, text=" + THÊM ", width=100, height=35, fg_color=ACCENT_GREEN, text_color="#000", 
                                            font=ctk.CTkFont(weight="bold"), command=self.add_manual_flower)
        self.btn_add_manual.pack(pady=(5, 0))

        # --- LỊCH SỬ ĐÃ NHẬP ---
        self.history_card = ctk.CTkFrame(self.input_card, fg_color="transparent")
        self.history_card.pack(fill="x", padx=20, pady=(0, 15))
        ctk.CTkLabel(self.history_card, text="Lịch sử nhập:", font=ctk.CTkFont(size=11, slant="italic"), text_color="#777").pack(side="left", padx=(0, 10))
        
        self.history_btns_frame = ctk.CTkFrame(self.history_card, fg_color="transparent")
        self.history_btns_frame.pack(side="left", fill="x", expand=True)
        
        self.update_history_ui()
        self.update_active_flower_ui()

    def update_history_ui(self):
        # Xóa các nút lịch sử cũ
        for widget in self.history_btns_frame.winfo_children():
            widget.destroy()
            
        history = self.get_history_data()[:8] # Lấy 8 cái gần nhất
        if not history:
            ctk.CTkLabel(self.history_btns_frame, text="(Trống)", font=ctk.CTkFont(size=10), text_color="#555").pack(side="left")
            return

        for item in history:
            name = item["name"]
            btn = ctk.CTkButton(self.history_btns_frame, text=name, height=22, width=20, 
                                font=ctk.CTkFont(size=10), fg_color="#222", hover_color="#333",
                                command=lambda x=item: self.fill_from_history(x))
            btn.pack(side="left", padx=2)

    def fill_from_history(self, item):
        self.ent_flower_name.delete(0, 'end')
        self.ent_flower_name.insert(0, item["name"])
        self.ent_harvest_count.delete(0, 'end')
        self.ent_harvest_count.insert(0, str(item.get("count", 1)))
        self.ent_harvest_interval.delete(0, 'end')
        self.ent_harvest_interval.insert(0, str(item.get("interval", 60)))
        self.var_cham_nhanh.set(item.get("cham_nhanh", False))
        self.var_trong_tay.set(item.get("trong_tay", False))

    def get_history_data(self):
        try:
            if os.path.exists("flower_history.json"):
                with open("flower_history.json", "r", encoding="utf-8") as f:
                    return json.load(f)
        except: pass
        return []

    def save_to_history(self, name, count, interval, cham_nhanh=False, trong_tay=False):
        history = self.get_history_data()
        # Loại bỏ nếu đã tồn tại để đẩy lên đầu
        history = [h for h in history if h["name"] != name]
        history.insert(0, {"name": name, "count": count, "interval": interval, "cham_nhanh": cham_nhanh, "trong_tay": trong_tay})
        try:
            with open("flower_history.json", "w", encoding="utf-8") as f:
                json.dump(history[:20], f, ensure_ascii=False, indent=4)
        except: pass

    def add_manual_flower(self):
        name = self.ent_flower_name.get().strip()
        count_str = self.ent_harvest_count.get().strip()
        interval_str = self.ent_harvest_interval.get().strip()
        cham_nhanh = self.var_cham_nhanh.get()
        trong_tay = self.var_trong_tay.get()
        
        if not name: return
        
        try:
            count = int(count_str)
            interval = int(interval_str)
        except: return
        
        # Lưu vào lịch sử và cập nhật UI lịch sử
        self.save_to_history(name, count, interval, cham_nhanh, trong_tay)
        self.update_history_ui()

        # Tạo flower object giả lập để dùng cho logic add_flower_task
        flower_obj = {"name": name, "cham_nhanh": cham_nhanh, "trong_tay": trong_tay}
        
        if len(self.flower_queue) >= 50:
            self.add_log("CẢNH BÁO: Hàng đợi trồng hoa đã đầy (5/5)!")
            return

        # Lưu vào queue UI của MainApp để hiển thị
        f_task = {
            "name": name,
            "_last_cnt": count,
            "_remaining_cnt": count,
            "_last_inter": interval
        }
        self.flower_queue.append(f_task)
        
        # Gửi task xuống các instances
        for worker in self.active_workers:
            worker.add_flower_task(flower_obj, count, interval)
            
        self.update_active_flower_ui()
        self.ent_flower_name.delete(0, 'end') # Xóa để nhập cái tiếp theo

    def update_active_flower_ui(self):
        # Tạo key để kiểm tra xem cấu trúc hàng đợi có thực sự thay đổi không
        queue_names = [f.get("name", "Unknown") for f in self.flower_queue]
        queue_key = "|".join(queue_names) + f"_{len(self.flower_queue)}"
        
        # Nếu cấu trúc hàng đợi thay đổi (thêm/bớt/đổi tên) -> Chỉ rebuild bên trong scroll frame
        if queue_key != getattr(self, "_last_queue_key", ""):
            self._last_queue_key = queue_key
            
            # Xóa các item cũ trong scroll frame
            for w in self.flower_scroll.winfo_children():
                w.destroy()
            self.flower_ui_items = []
                
            if not self.flower_queue:
                ctk.CTkLabel(self.flower_scroll, text="CHƯA CÓ HOA TRONG HÀNG ĐỢI", font=ctk.CTkFont(size=14, weight="bold"), text_color="#666").pack(pady=30)
            else:
                for idx, f in enumerate(self.flower_queue):
                    content = ctk.CTkFrame(self.flower_scroll, fg_color="#222" if idx == 0 else "#1A1A1A", corner_radius=8)
                    content.pack(fill="x", padx=5, pady=2)
                    ctk.CTkLabel(content, text=f"{idx+1}.", font=ctk.CTkFont(size=12, weight="bold"), width=30).pack(side="left", padx=10)
                    
                    info_area = ctk.CTkFrame(content, fg_color="transparent")
                    info_area.pack(side="left", padx=10, expand=True, fill="x")
                    
                    name_color = ACCENT_GREEN if idx == 0 else "#EEE"
                    lbl_name = ctk.CTkLabel(info_area, text="", font=ctk.CTkFont(size=13, weight="bold"), text_color=name_color)
                    lbl_name.pack(side="left")
                    
                    lbl_status = ctk.CTkLabel(info_area, text="", font=ctk.CTkFont(size=11), text_color="#AAA")
                    lbl_status.pack(side="right", padx=15)
                    
                    self.flower_ui_items.append({"name": lbl_name, "status": lbl_status})

        # --- PHẦN UPDATE DATA (Luôn mượt vì chỉ update text) ---
        if hasattr(self, "lbl_queue_count"):
             self.lbl_queue_count.configure(text=f"HÀNG ĐỢI TRỒNG HOA ({len(self.flower_queue)}/50)")

        for idx, f in enumerate(self.flower_queue):
            if idx < len(self.flower_ui_items):
                status_suffix = " (ĐANG TRỒNG)" if idx == 0 else " (ĐANG ĐỢI)"
                name_text = f.get("name", "Unknown").upper() + status_suffix
                # Chỉ configure nếu text thực sự khác để tối ưu
                if self.flower_ui_items[idx]["name"].cget("text") != name_text:
                    self.flower_ui_items[idx]["name"].configure(text=name_text)
                
                cnt = f.get('_remaining_cnt', f.get('_last_cnt', 1))
                total = f.get('_last_cnt', 1)
                inter = f.get('_last_inter', 60)
                status_str = f"Lần {total - cnt + 1}/{total} (Mỗi {inter}s)"
                if self.flower_ui_items[idx]["status"].cget("text") != status_str:
                    self.flower_ui_items[idx]["status"].configure(text=status_str)

    def stop_flower_planting_all(self):
        self.add_log("HỆ THỐNG: Dừng và xóa sạch hàng đợi trồng hoa.")
        self.flower_queue = []
        self.update_active_flower_ui()
        for worker in self.active_workers:
            worker.flower_queue = []
            worker.stop_flower_task()

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
            
            # ĐỒNG BỘ HÀNG ĐỢI UI (Lấy máy đầu tiên làm chuẩn để hiển thị)
            if self.active_workers and self.flower_queue:
                worker0 = self.active_workers[0]
                # Nếu máy 1 đã làm xong bớt hoa trong hàng đợi
                if len(worker0.flower_queue) < len(self.flower_queue):
                    # Cập nhật lại hàng đợi UI cho khớp với số lượng còn lại của máy
                    diff = len(self.flower_queue) - len(worker0.flower_queue)
                    for _ in range(diff):
                        if self.flower_queue: self.flower_queue.pop(0)
                    self.update_active_flower_ui()
            
            # 2. Đồng bộ số lần thu hoạch còn lại của hoa đang trồng (Lấy máy 1 làm chuẩn)
            if self.active_workers and self.flower_queue:
                w0 = self.active_workers[0]
                if w0.flower_queue:
                    ui_flower = self.flower_queue[0]
                    wk_flower = w0.flower_queue[0]
                    if ui_flower.get("_remaining_cnt") != wk_flower["harvest_count"]:
                        ui_flower["_remaining_cnt"] = wk_flower["harvest_count"]
                        self.update_active_flower_ui()

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
            print(f"DEBUG ADB RAW: {res.stdout.strip()}")
            
            # Nếu ADB server chưa chạy, subprocess sẽ tự động start nó. 
            # Chỉ khi lỗi nặng mới cần kill-server thủ công.
            
            lines = res.stdout.strip().split('\n')
            temp_serials = []
            for line in lines:
                line = line.strip()
                if not line or "List of devices attached" in line or "* daemon" in line:
                    continue
                
                parts = line.split()
                if len(parts) >= 2:
                    serial = parts[0].strip()
                    status = parts[1].strip()
                    
                    if status == "device":
                        temp_serials.append(serial)
                    elif status == "offline":
                        offline_count += 1
                    elif status == "unauthorized":
                        unauthorized_count += 1

            # Lọc trùng lặp chuyên sâu (Dành cho LDPlayer: Console port và ADB port)
            seen_instances = set()
            for serial in temp_serials:
                # Trích xuất port số
                port_str = None
                if "emulator-" in serial:
                    port_str = serial.split("-")[-1]
                elif ":" in serial:
                    port_str = serial.split(":")[-1]
                
                if port_str and port_str.isdigit():
                    p_val = int(port_str)
                    # LDPlayer mặc định: Port 5554/5555 là máy 0, 5556/5557 là máy 1...
                    # Chuẩn hóa về chỉ số máy: (port - 5554) // 2
                    inst_idx = (p_val - 5554) // 2 if p_val >= 5554 else p_val
                    
                    if inst_idx not in seen_instances:
                        seen_instances.add(inst_idx)
                        device_serials.append(serial)
                else:
                    # Thiết bị thật hoặc không có port
                    if serial not in seen_instances:
                        seen_instances.add(serial)
                        device_serials.append(serial)
            
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
            card.grid(row=i // 12, column=i % 12, padx=1, pady=1, sticky="nsew")
            
            # Tách lấy port hoặc phần số cuối cùng của Serial
            display_name = serial.replace("emulator-", "").split(":")[-1]
            name_lbl = ctk.CTkLabel(card, text=display_name, font=ctk.CTkFont(size=9, weight="bold"))
            name_lbl.pack(pady=(2, 0))
            
            status_lbl = ctk.CTkLabel(card, text="Sẵn sàng", font=ctk.CTkFont(size=8), text_color="#666")
            status_lbl.pack(pady=(0, 2))
            
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
            # Truyền cấu hình checkbox vào worker
            worker.enabled_tasks_vars = self.enabled_tasks
            
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
        self.title("KÍCH HOẠT Tool Mr Thanh - Thế Giới Hoa Viên")
        self.geometry("500x550")
        self.resizable(False, False)
        self.configure(fg_color=BG_COLOR)
        
        self.hwid = get_hwid()
        self.setup_ui()

    def setup_ui(self):
        # Logo & Title
        ctk.CTkLabel(self, text="Tool Mr Thanh - Thế Giới Hoa Viên", font=ctk.CTkFont(size=24, weight="bold"), text_color=ACCENT_GREEN).pack(pady=(40, 10))
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


# pyinstaller --noconfirm --onefile --windowed --name "Tool Mr Thanh - Thế Giới Hoa Viên" --add-data "images;images" --add-data "logo.png;." --add-data "start.png;." --add-data "stop.png;." gui_tool.py
