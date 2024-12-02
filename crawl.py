from selenium import webdriver
from selenium.webdriver.remote.webdriver import WebDriver
from selenium.webdriver.common.action_chains import ActionChains
import json
import pprint
import argparse

from Classes import *

# 1. Handling command line arguments
parser = argparse.ArgumentParser(description='Crawler')
parser.add_argument("--debug", action='store_true', help="Dont use path deconstruction and recon scan. Good for testing single URL")
parser.add_argument("--url", help="Custom URL to crawl")
args = parser.parse_args()

# 2. Clean form_files/dynamic
root_dirname = os.path.dirname(__file__)
dynamic_path = os.path.join(root_dirname, 'form_files', 'dynamic')
for f in os.listdir(dynamic_path):
    os.remove(os.path.join(dynamic_path, f))

# 3. Add script function is added to WebDriver
WebDriver.add_script = add_script

# 4. Init Chrome browser settings
chrome_options = webdriver.ChromeOptions()
chrome_options.add_argument("--disable-web-security")   # To bypass limitations like resource load
chrome_options.add_argument("--disable-xss-auditor")    # To detect XSS script

# launch Chrome
driver = webdriver.Chrome(chrome_options = chrome_options)
#driver.set_window_position(-1700,0)

# 5. Read scripts and add script which will be executed when the page starts loading
## JS libraries from JaK crawler, with minor improvements
driver.add_script( open("js/lib.js", "r").read() )          # JS library
driver.add_script( open("js/property_obs.js", "r").read() ) # Track the state changes of DOM element properties
driver.add_script( open("js/md5.js", "r").read() )          # Hash script
driver.add_script( open("js/addeventlistener_wrapper.js", "r").read() ) # Wrapping event_listenr
driver.add_script( open("js/timing_wrapper.js", "r").read() )   # Record times of loading, ...
driver.add_script( open("js/window_wrapper.js", "r").read() )   # Record state changes of window element
## Black Widow additions
driver.add_script( open("js/forms.js", "r").read() )        # Extract Form data
driver.add_script( open("js/xss_xhr.js", "r").read() )      # Detect XSS vulnerabilities
driver.add_script( open("js/remove_alerts.js", "r").read() )    # Remove alerts from page

if args.url:
    url = args.url
    Crawler(driver, url).start(args.debug)
else:
    print("Please use --url")




