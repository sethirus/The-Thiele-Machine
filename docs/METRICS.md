# Thiele Receipts: Adoption Metrics

This document tracks adoption metrics for the Thiele receipt system to measure impact and guide development.

## Tracking Methodology

All metrics are **manually logged** from public sources. No user data is collected automatically.

**Data Sources:**
- PyPI download stats (public)
- Docker Hub pull counts (public)
- GitHub release download counts (public)
- GitHub Stars/Forks (public)

**Update Frequency:** Monthly snapshot (first week of each month)

---

## Release Metrics

| Release Tag | Date | Downloads | Receipts Included | Notes |
|-------------|------|-----------|-------------------|-------|
| v1.0.0 (planned) | TBD | - | ✅ Yes | First production release with signed receipts |

---

## Distribution Metrics

### PyPI Downloads

| Month | Package | Downloads | Notes |
|-------|---------|-----------|-------|
| 2025-01 (planned) | `thiele-replay` | - | Package not yet published |

**PyPI URL:** https://pypi.org/project/thiele-replay/ (pending publication)

### Docker Hub Pulls

| Month | Image | Pulls | Notes |
|-------|-------|-------|-------|
| 2025-01 (planned) | `sethirus/thiele-receipts` | - | Image not yet published |

**Docker Hub URL:** https://hub.docker.com/r/sethirus/thiele-receipts (pending publication)

### Homebrew Installations

| Month | Formula | Installs | Notes |
|-------|---------|----------|-------|
| 2025-01 (planned) | `thiele-receipts` | - | Formula not yet in tap |

**Homebrew Tap:** `sethirus/tap/thiele-receipts` (pending publication)

---

## Repository Metrics

| Metric | Count | Last Updated |
|--------|-------|--------------|
| GitHub Stars | - | Manual update |
| GitHub Forks | - | Manual update |
| GitHub Watchers | - | Manual update |
| Open Issues | - | Manual update |
| Contributors | 1 | 2025-01-04 |

---

## Project Usage

### Projects Using Receipts

| Project | Implementation | Status | Notes |
|---------|---------------|--------|-------|
| The Thiele Machine | GitHub Action + Manual | ✅ Dogfooding | Self-hosting receipts for all releases |
| (Add your project) | - | - | Open an issue to be listed here |

**Want to be listed?** Open an issue or PR adding your project above.

---

## Web Tool Usage

### Browser Tools (Estimated)

*Note: No analytics are collected. These are based on GitHub Pages traffic (if available).*

| Tool | Purpose | Notes |
|------|---------|-------|
| Create Receipt | Browser-based receipt generation | No analytics tracking |
| Verify Receipt | Browser-based receipt verification | No analytics tracking |
| Badge Generator | README badge creation | No analytics tracking |
| QR Generator | QR code generation | No analytics tracking |

---

## Trends and Analysis

### Month 1 (Baseline)

**Status:** Pre-launch  
**Focus:** Complete Phase 4-7 implementation, prepare for v1.0.0 release

**Planned Milestones:**
- [ ] Publish PyPI package
- [ ] Publish Docker image
- [ ] Submit Homebrew formula
- [ ] Release v1.0.0 with signed receipts
- [ ] Update README with verification instructions

### Month 2 (Target)

**Goals:**
- PyPI downloads: 10+ (initial adoption)
- Docker pulls: 5+ (early adopters)
- GitHub Stars: +5 (organic growth)
- 1-2 external projects using receipts

### Month 3 (Target)

**Goals:**
- PyPI downloads: 50+ (growing adoption)
- Docker pulls: 20+ (container users)
- GitHub Stars: +10 (community interest)
- 3-5 external projects using receipts

### 6-Month Target

**Success Criteria:**
- 100+ PyPI downloads/month (sustained usage)
- 50+ Docker pulls/month (container adoption)
- 10+ external projects using receipts (ecosystem growth)
- 1-2 blog posts/articles mentioning receipts (awareness)

---

## Key Performance Indicators

### Leading Indicators (Early Signals)

- ✅ Documentation completeness (100%)
- ✅ Browser tools availability (4/4 tools live)
- ✅ CI integration templates (2+ examples)
- ⏳ PyPI package publication (pending)
- ⏳ Docker image publication (pending)

### Lagging Indicators (Outcome Measures)

- Downloads per month (PyPI + Docker)
- External project adoption count
- GitHub engagement (stars, forks, issues)
- Community contributions (PRs, issues, discussions)

---

## Feedback Tracking

### Common Questions

| Question | Count | Answer |
|----------|-------|--------|
| "How do I verify a receipt?" | - | Link to [User Quickstart](for-users-quickstart.md) |
| "How do I add receipts to my project?" | - | Link to [Maintainer Quickstart](for-maintainers-quickstart.md) |
| "What's the difference from checksums?" | - | Receipts include full hash chain + optional signatures |

### Feature Requests

| Feature | Votes | Status | Notes |
|---------|-------|--------|-------|
| Example request | - | - | Track via GitHub issues |

**Submit requests:** https://github.com/sethirus/The-Thiele-Machine/issues

---

## Monthly Update Template

Copy this template for monthly updates:

```markdown
## YYYY-MM Update

**Date:** YYYY-MM-DD

### Distribution
- PyPI downloads: X (+Y from last month)
- Docker pulls: X (+Y from last month)
- Homebrew installs: X (+Y from last month)

### Repository
- Stars: X (+Y)
- Forks: X (+Y)
- Issues: X open, Y closed this month

### Projects
- New projects using receipts: X
- Total projects tracked: X

### Highlights
- [Key achievement 1]
- [Key achievement 2]

### Action Items
- [ ] [Action needed]
- [ ] [Action needed]
```

---

## Interpretation Guidelines

### What Good Looks Like

**Healthy Growth:**
- Steady month-over-month increase in downloads (10-20% growth)
- New projects adopting receipts (1-2 per quarter)
- Active community engagement (issues, PRs, discussions)
- Positive sentiment in feedback

**Warning Signs:**
- Downloads plateau or decline for 2+ months
- Zero external adoption after 6 months
- High issue-to-PR ratio (problems but no contributions)
- Negative feedback about usability

### Response Plan

**If downloads are flat:**
- Review and improve documentation
- Create tutorial videos or blog posts
- Reach out to potential users directly
- Add more examples and use cases

**If adoption is slow:**
- Lower the barrier to entry (simpler installation)
- Create more CI templates for popular platforms
- Present at conferences or write articles
- Partner with related projects

**If feedback is negative:**
- Prioritize UX improvements
- Address common pain points
- Improve error messages and debugging
- Add more hand-holding in docs

---

## Privacy and Ethics

**Data Collection:**
- ✅ All metrics are from **public sources only**
- ✅ No user tracking or analytics
- ✅ No personal data collection
- ✅ Transparent methodology

**Opt-Out:**
Users can opt out of public download stats by:
- Using private Docker registries
- Installing from source instead of PyPI
- Building packages locally

---

## Contributing to Metrics

Help us track adoption!

1. **Using receipts in your project?** Add it to the "Projects Using Receipts" table via PR
2. **See receipts mentioned?** Note the link in an issue
3. **Have usage data?** Share anonymized stats in an issue

---

## Next Review

**Next update due:** First week of the month following v1.0.0 release

**Reviewer:** Project maintainer (@sethirus)

**Process:**
1. Collect data from public sources
2. Update tables above
3. Write monthly summary
4. Identify trends and action items
5. Commit to repository

---

**Last Updated:** 2025-01-04 (Initial template created)  
**Next Update:** TBD (after v1.0.0 release + 1 month)
