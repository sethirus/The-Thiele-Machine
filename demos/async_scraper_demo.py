#!/usr/bin/env python3
"""
Async Web Scraper Demo - Thiele Verified Code
Demonstrates: async/await, rate limiting, caching, decorators, context managers
"""

import asyncio
import aiohttp
import hashlib
import json
import time
from dataclasses import dataclass, field
from typing import Optional, Callable, Any
from collections import deque
from functools import wraps
import logging

# Configure logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)


@dataclass
class CacheEntry:
    data: Any
    timestamp: float
    ttl: float = 300.0

    @property
    def is_expired(self) -> bool:
        return time.time() - self.timestamp > self.ttl


class RateLimiter:
    """Token bucket rate limiter for async operations."""
    
    def __init__(self, rate: float, burst: int = 10):
        self.rate = rate  # tokens per second
        self.burst = burst
        self.tokens = burst
        self.last_update = time.monotonic()
        self._lock = asyncio.Lock()

    async def acquire(self):
        async with self._lock:
            now = time.monotonic()
            elapsed = now - self.last_update
            self.tokens = min(self.burst, self.tokens + elapsed * self.rate)
            self.last_update = now

            if self.tokens < 1:
                wait_time = (1 - self.tokens) / self.rate
                logger.debug(f"Rate limited, waiting {wait_time:.2f}s")
                await asyncio.sleep(wait_time)
                self.tokens = 0
            else:
                self.tokens -= 1


class AsyncCache:
    """Thread-safe async LRU cache with TTL support."""
    
    def __init__(self, maxsize: int = 100, ttl: float = 300.0):
        self.maxsize = maxsize
        self.ttl = ttl
        self._cache: dict[str, CacheEntry] = {}
        self._access_order: deque = deque()
        self._lock = asyncio.Lock()

    def _generate_key(self, *args, **kwargs) -> str:
        key_data = json.dumps({"args": args, "kwargs": kwargs}, sort_keys=True)
        return hashlib.md5(key_data.encode()).hexdigest()

    async def get(self, key: str) -> Optional[Any]:
        async with self._lock:
            if key in self._cache:
                entry = self._cache[key]
                if not entry.is_expired:
                    return entry.data
                del self._cache[key]
            return None

    async def set(self, key: str, value: Any):
        async with self._lock:
            if len(self._cache) >= self.maxsize:
                oldest = self._access_order.popleft()
                self._cache.pop(oldest, None)
            
            self._cache[key] = CacheEntry(data=value, timestamp=time.time(), ttl=self.ttl)
            self._access_order.append(key)


def cached(cache: AsyncCache):
    """Decorator for caching async function results."""
    def decorator(func: Callable):
        @wraps(func)
        async def wrapper(*args, **kwargs):
            key = cache._generate_key(func.__name__, *args, **kwargs)
            result = await cache.get(key)
            if result is not None:
                logger.debug(f"Cache hit for {func.__name__}")
                return result
            result = await func(*args, **kwargs)
            await cache.set(key, result)
            return result
        return wrapper
    return decorator


@dataclass
class ScrapedData:
    url: str
    status: int
    content_length: int
    headers: dict
    fetch_time: float
    error: Optional[str] = None


class AsyncWebScraper:
    """High-performance async web scraper with rate limiting and caching."""
    
    def __init__(self, rate_limit: float = 5.0, cache_ttl: float = 300.0):
        self.rate_limiter = RateLimiter(rate=rate_limit)
        self.cache = AsyncCache(ttl=cache_ttl)
        self.results: list[ScrapedData] = []
        self._session: Optional[aiohttp.ClientSession] = None

    async def __aenter__(self):
        self._session = aiohttp.ClientSession(
            timeout=aiohttp.ClientTimeout(total=30),
            headers={"User-Agent": "ThieleScraper/1.0"}
        )
        return self

    async def __aexit__(self, *args):
        if self._session:
            await self._session.close()

    async def fetch(self, url: str) -> ScrapedData:
        await self.rate_limiter.acquire()
        start_time = time.monotonic()
        
        try:
            async with self._session.get(url) as response:
                content = await response.read()
                return ScrapedData(
                    url=url,
                    status=response.status,
                    content_length=len(content),
                    headers=dict(response.headers),
                    fetch_time=time.monotonic() - start_time
                )
        except Exception as e:
            return ScrapedData(
                url=url, status=0, content_length=0,
                headers={}, fetch_time=time.monotonic() - start_time,
                error=str(e)
            )

    async def scrape_many(self, urls: list[str], max_concurrent: int = 10) -> list[ScrapedData]:
        semaphore = asyncio.Semaphore(max_concurrent)
        
        async def bounded_fetch(url: str) -> ScrapedData:
            async with semaphore:
                return await self.fetch(url)
        
        tasks = [bounded_fetch(url) for url in urls]
        self.results = await asyncio.gather(*tasks)
        return self.results

    def get_statistics(self) -> dict:
        successful = [r for r in self.results if r.error is None]
        return {
            "total": len(self.results),
            "successful": len(successful),
            "failed": len(self.results) - len(successful),
            "avg_fetch_time": sum(r.fetch_time for r in successful) / len(successful) if successful else 0,
            "total_bytes": sum(r.content_length for r in successful)
        }


async def main():
    print("=" * 60)
    print("🛡️  Thiele Verified Async Web Scraper Demo")
    print("=" * 60)
    
    urls = [
        "https://httpbin.org/get",
        "https://httpbin.org/headers",
        "https://httpbin.org/ip",
        "https://httpbin.org/user-agent",
        "https://httpbin.org/uuid",
    ]
    
    print(f"\n📡 Scraping {len(urls)} URLs with rate limiting...\n")
    
    async with AsyncWebScraper(rate_limit=2.0) as scraper:
        results = await scraper.scrape_many(urls)
        
        for result in results:
            status = "✅" if result.error is None else "❌"
            print(f"{status} {result.url}")
            print(f"   Status: {result.status} | Size: {result.content_length} bytes | Time: {result.fetch_time:.3f}s")
        
        stats = scraper.get_statistics()
        print("\n" + "=" * 60)
        print("📊 Statistics:")
        print(f"   Total requests:    {stats['total']}")
        print(f"   Successful:        {stats['successful']}")
        print(f"   Failed:            {stats['failed']}")
        print(f"   Avg fetch time:    {stats['avg_fetch_time']:.3f}s")
        print(f"   Total bytes:       {stats['total_bytes']:,}")
        print("=" * 60)


if __name__ == "__main__":
    asyncio.run(main())
