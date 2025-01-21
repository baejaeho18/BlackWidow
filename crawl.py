from selenium import webdriver
from selenium.webdriver.remote.webdriver import WebDriver
from selenium.webdriver.common.action_chains import ActionChains
import json
import pprint
import argparse

from Classes import *

parser = argparse.ArgumentParser(description='Crawler')
parser.add_argument("--debug", action='store_true', help="Dont use path deconstruction and recon scan. Good for testing single URL")
parser.add_argument("--url", help="Custom URL to crawl")
parser.add_argument("--t", type=int, default=900, help="Set timeout in seconds")
parser.add_argument("--q", default="queue.txt", help="Path to queue file")
parser.add_argument("--range", help="Range of queue and output files in the format start-end (e.g., 100-200)")
parser.add_argument("--o", default="script_logs.xlsx", help="Output log file name")
args = parser.parse_args()

# Determine queue and output file names based on the range
if args.range:
    range_start, range_end = args.range.split('-')
    queue_file = f"queue({range_start}-{range_end}).txt"
    output_file = f"script_logs({range_start}-{range_end}).xlsx"
else:
    queue_file = "queue.txt"
    output_file = "script_logs.xlsx"

# Clean form_files/dynamic
root_dirname = os.path.dirname(__file__)
dynamic_path = os.path.join(root_dirname, 'form_files', 'dynamic')
for f in os.listdir(dynamic_path):
    os.remove(os.path.join(dynamic_path, f))

WebDriver.add_script = add_script

chrome_options = webdriver.ChromeOptions()
chrome_options.add_argument("--disable-web-security")
chrome_options.add_argument("--disable-xss-auditor")
chrome_options.add_argument("--headless")
# launch Chrome
driver = webdriver.Chrome(options = chrome_options)
#driver.set_window_position(-1700,0)

# Read scripts and add script which will be executed when the page starts loading
## JS libraries from JaK crawler, with minor improvements
driver.add_script( open("js/lib.js", "r").read() )
driver.add_script( open("js/property_obs.js", "r").read() )
driver.add_script( open("js/md5.js", "r").read() )
driver.add_script( open("js/addeventlistener_wrapper.js", "r").read() )
driver.add_script( open("js/timing_wrapper.js", "r").read() )
driver.add_script( open("js/window_wrapper.js", "r").read() )
# Black Widow additions
driver.add_script( open("js/forms.js", "r").read() )
driver.add_script( open("js/xss_xhr.js", "r").read() )
driver.add_script( open("js/remove_alerts.js", "r").read() )

def monitor_output_file(file_path, timeout):
    """Monitor output file for changes within the given timeout."""
    js_output_dir = os.path.join(os.getcwd(), "js_output")
    full_path = os.path.join(js_output_dir, file_path)

    start_time = time.time()
    while time.time() - start_time < timeout:
        if os.path.exists(full_path):
            if time.time() - os.path.getmtime(full_path) < timeout:
                return True
        time.sleep(5)
    return False

def process_url(driver, url, output_file, timeout):
    """Process a single URL."""
    try:
        Crawler(driver, url, timeout, output_file).start(args.debug)
        if monitor_output_file(output_file, timeout):
            return True
    except Exception as e:
        print(f"Error processing {url}: {e}")
    return False

def update_queue_file(queue_file, undone_file, url, success):
    """Update the queue file and undone file based on the result."""
    with open(queue_file, "r") as f:
        lines = f.readlines()
    with open(queue_file, "w") as f:
        for line in lines:
            if line.strip() != url:
                f.write(line)
    if not success:
        with open(undone_file, "a") as f:
            f.write(f"{url}\n")

# Main logic
if args.url:
    process_url(driver, args.url, output_file, args.t)
else:
    undone_file = "undone.txt"
    try:
        with open(queue_file, "r") as f:
            urls = [line.strip() for line in f if line.strip()]
        for url in urls:
            print(f"Crawling: {url}")
            success = process_url(driver, url, output_file, args.t)
            update_queue_file(queue_file, undone_file, url, success)
    except FileNotFoundError:
        print("Please use --url or --range")
