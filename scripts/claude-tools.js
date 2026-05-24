// A library of helper functions for Playwright to interact with Claude Code UI.
// Use these snippets with browser_run_code_unsafe.

const ClaudeTools = {
  // Send a message in the active chat
  sendChatMessage: async (page, message) => {
    const prompt = page.locator('div[contenteditable="true"]');
    await prompt.fill(message);
    await prompt.press('Enter');
  },

  // Click on a specific session by its name in the sidebar
  selectSession: async (page, sessionName) => {
    await page.locator(`text="${sessionName}"`).click();
  },

  // Extract the latest response from Claude
  getLatestResponse: async (page) => {
    // This selector might need to be adjusted based on the actual DOM structure of Claude's messages
    const responses = page.locator('.font-claude-message');
    const count = await responses.count();
    if (count > 0) {
      return await responses.nth(count - 1).innerText();
    }
    return null;
  }
};

// Example usage for browser_run_code_unsafe:
/*
async (page) => {
  const prompt = page.locator('div[contenteditable="true"]');
  await prompt.fill('Hello Claude!');
  await prompt.press('Enter');
}
*/
