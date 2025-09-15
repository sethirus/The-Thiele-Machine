#!/usr/bin/env python3
"""Test browser launch"""

from playwright.sync_api import sync_playwright

with sync_playwright() as p:
    browser = p.chromium.launch(headless=True)
    page = browser.new_page()
    page.goto("https://example.com")
    page.screenshot(path="test_screenshot.png")
    print("Browser test successful")
    browser.close()